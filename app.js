'use strict';

// Die 16 Würfel mit deutscher Buchstabenverteilung (je 6 Seiten). "Q" wird als "Qu" angezeigt.
const DICE = [
  'ETUKNO', 'EVGTIN', 'DECAMP', 'IELRUW',
  'EHIFSE', 'RECALS', 'ENTDOS', 'OFXRIA',
  'NAVEDZ', 'EIOATA', 'GLENYU', 'BMAQJO',
  'TLIBRA', 'SPULTE', 'AIMSOR', 'ENHRIS',
];

const DEFAULT_SECONDS = 120;
const MIN_SECONDS = 10;
const MAX_SECONDS = 59 * 60 + 59;
const LOW_SECONDS = 10;
const BOARD_SIZES = [4, 5, 6];
const THEMES = ['classic', 'wood', 'neon'];
const DURATION_KEY = 'raschel.roundSeconds';
const SIZE_KEY = 'raschel.boardSize';
const THEME_KEY = 'raschel.theme';
const TOP_WORDS = 10;
const MAX_CHECKED_WORDS = 300; // höchstens so viele lange Wörter auf eine Definition prüfen
const LOOKUP_BATCH = 8;     // gleichzeitige Wiktionary-Abfragen
const COMMON_WORD_COUNT = 200; // ab so vielen Vorkommen gilt ein Fachwort als alltäglich

const boardEl = document.getElementById('board');
const timerEl = document.getElementById('timer');
const startBtn = document.getElementById('start');
const showWordsBtn = document.getElementById('show-words');
const resultsEl = document.getElementById('results');
const resultsStatusEl = document.getElementById('results-status');
const wordListEl = document.getElementById('word-list');
const definitionEl = document.getElementById('definition');
const defWordEl = document.getElementById('def-word');
const defTextEl = document.getElementById('def-text');
const defExampleEl = document.getElementById('def-example');
const defLinksEl = document.getElementById('def-links');
const defLinkEl = document.getElementById('def-link');
const defDudenEl = document.getElementById('def-duden');
const menuEl = document.getElementById('menu');
const gameEl = document.getElementById('game');
const playBtn = document.getElementById('play');
const menuBtn = document.getElementById('menu-btn');
const minutesInput = document.getElementById('minutes');
const secondsInput = document.getElementById('seconds');
const sizeOptionsEl = document.getElementById('size-options');
const themeOptionsEl = document.getElementById('theme-options');
const themeColorMeta = document.querySelector('meta[name="theme-color"]');

let roundSeconds = DEFAULT_SECONDS;
let boardSize = 4;
let neighbors = [];        // Nachbarfelder je Feld, abhängig von der Feldgröße
let dieEls = [];
let letters = [];          // aktuelles Feld ('Q' = "Qu")
let endTime = 0;
let tickId = null;
let shakeId = null;
let audioCtx = null;
let wakeLock = null;
let started = false;
let dictionary = null;     // Promise<string[]>, wird erst bei Bedarf geladen
const definitions = new Map(); // Wort -> Promise<{ title, meaning, … }>
let definitionRequest = 0;
let roundId = 0;
let lastResults = null;    // { words, status } der letzten "Längste Wörter"-Liste, für Zuschauer

const randomInt = (n) => Math.floor(Math.random() * n);

function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = randomInt(i + 1);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function loadSetting(key) {
  try { return localStorage.getItem(key); } catch { return null; }
}

function saveSetting(key, value) {
  try { localStorage.setItem(key, value); } catch { /* ohne Speicher */ }
}

// Nachbarfelder inkl. Diagonalen (so dürfen Wörter verbunden werden)
function buildNeighbors(n) {
  return Array.from({ length: n * n }, (_, i) => {
    const r = Math.floor(i / n);
    const c = i % n;
    const out = [];
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        const rr = r + dr;
        const cc = c + dc;
        if ((dr || dc) && rr >= 0 && rr < n && cc >= 0 && cc < n) out.push(rr * n + cc);
      }
    }
    return out;
  });
}

// --- Würfeln -------------------------------------------------------------------

// 4x4 nutzt die 16 Original-Würfel; größere Felder zusätzlich zufällig gewählte Kopien davon,
// damit die Buchstabenverteilung deutsch bleibt (5x5: 16 + 9, 6x6: 16 + 16 + 4)
function diceForBoard(cells) {
  const dice = [];
  while (dice.length < cells) dice.push(...shuffle([...DICE]).slice(0, cells - dice.length));
  return dice;
}

// Damit das Feld spielbar wird: Vokalanzahl begrenzen, seltene Buchstaben begrenzen und die
// Würfel so anordnen, dass typische deutsche Buchstabenpaare (er, en, ch, st, ei …) nebeneinander
// liegen. Laut Simulation liefert das auf 4x4 etwa 2,7-mal so viele Wörter wie zufällig gelegte Würfel.
const VOWELS = new Set(['A', 'E', 'I', 'O', 'U']);
const RARE_LETTERS = new Set(['Q', 'X', 'Y', 'J', 'V']);
const MIN_VOWEL_SHARE = 0.25;  // 4x4: 4 Vokale
const MAX_VOWEL_SHARE = 0.375; // 4x4: 6 Vokale
const ARRANGE_STEPS_PER_CELL = 25; // Tauschversuche je Feld (4x4: 400)

let edges = []; // alle Nachbarpaare [a, b] mit a < b, abhängig von der Feldgröße

// Wie typisch liegen die Buchstaben zweier Felder nebeneinander? (aus data/bigrams.js)
function pairScore(a, b) {
  return BIGRAM_SCORES[a < b ? a + b : b + a];
}

function boardScore(faces) {
  let score = 0;
  for (const [a, b] of edges) score += pairScore(faces[a], faces[b]);
  return score;
}

// Zufällig auslegen, dann Würfel tauschen, solange das Feld dadurch nicht schlechter wird
function arrangeByPairs(faces) {
  shuffle(faces);
  let score = boardScore(faces);
  const steps = ARRANGE_STEPS_PER_CELL * faces.length;
  for (let step = 0; step < steps; step++) {
    const i = randomInt(faces.length);
    const j = randomInt(faces.length);
    if (faces[i] === faces[j]) continue;
    [faces[i], faces[j]] = [faces[j], faces[i]];
    const next = boardScore(faces);
    if (next >= score) score = next;
    else [faces[i], faces[j]] = [faces[j], faces[i]];
  }
  return faces;
}

// Würfel mischen und werfen; Würfe mit zu wenigen/vielen Vokalen oder zu vielen seltenen
// Buchstaben (Q, X, Y, J, V) werden wiederholt
function rollBoard() {
  const cells = boardSize * boardSize;
  const minVowels = Math.round(cells * MIN_VOWEL_SHARE);
  const maxVowels = Math.round(cells * MAX_VOWEL_SHARE);
  const maxRare = Math.max(1, Math.floor(cells / 16)); // 4x4 und 5x5: 1, 6x6: 2
  let faces;
  let vowels;
  let rare;
  do {
    faces = diceForBoard(cells).map((die) => die[randomInt(6)]);
    vowels = faces.filter((l) => VOWELS.has(l)).length;
    rare = faces.filter((l) => RARE_LETTERS.has(l)).length;
  } while (vowels < minVowels || vowels > maxVowels || rare > maxRare);
  return arrangeByPairs(faces);
}

// --- Spielfeld ---------------------------------------------------------------

function buildBoard(n) {
  neighbors = buildNeighbors(n);
  edges = neighbors.flatMap((list, a) => list.filter((b) => a < b).map((b) => [a, b]));
  boardEl.style.setProperty('--n', n);
  dieEls = Array.from({ length: n * n }, () => {
    const die = document.createElement('div');
    die.className = 'die';
    const face = document.createElement('div');
    face.className = 'face';
    die.append(face);
    return die;
  });
  boardEl.replaceChildren(...dieEls);
  letters = [];
}

function renderBoard(faces) {
  faces.forEach((letter, i) => {
    const face = dieEls[i].firstChild;
    face.textContent = letter === 'Q' ? 'Qu' : letter;
    face.classList.toggle('qu', letter === 'Q');
  });
}

function highlightPath(path) {
  dieEls.forEach((die) => {
    die.classList.remove('hl');
    die.querySelector('.step')?.remove();
  });
  (path || []).forEach((cell, i) => {
    const step = document.createElement('span');
    step.className = 'step';
    step.textContent = i + 1;
    dieEls[cell].classList.add('hl');
    dieEls[cell].append(step);
  });
}

// --- Runde -------------------------------------------------------------------

function formatTime(sec) {
  return `${Math.floor(sec / 60)}:${String(sec % 60).padStart(2, '0')}`;
}

function tick() {
  const remaining = Math.max(0, Math.ceil((endTime - Date.now()) / 1000));
  timerEl.textContent = formatTime(remaining);
  timerEl.classList.toggle('low', remaining > 0 && remaining <= LOW_SECONDS);
  if (remaining === 0) endRound();
}

function resetTimerDisplay() {
  timerEl.hidden = false;
  timerEl.className = 'timer';
  timerEl.textContent = formatTime(roundSeconds);
}

function startRound() {
  if (tickId && !confirm('Laufende Runde abbrechen und neu würfeln?')) return;

  unlockAudio();
  requestWakeLock();
  started = true;
  roundId++;
  clearInterval(tickId);
  tickId = null;
  resetTimerDisplay();
  startBtn.disabled = true;
  showWordsBtn.hidden = true;
  resultsEl.hidden = true;
  lastResults = null;
  hideDefinition();
  highlightPath(null);

  // Kurzes "Schütteln", danach liegt das Feld fest und der Timer läuft
  boardEl.classList.add('shaking');
  let frames = 0;
  clearInterval(shakeId);
  shakeId = setInterval(() => {
    letters = rollBoard();
    renderBoard(letters);
    if (++frames < 8) return;
    clearInterval(shakeId);
    shakeId = null;
    boardEl.classList.remove('shaking');
    endTime = Date.now() + roundSeconds * 1000;
    tickId = setInterval(tick, 250);
    tick();
    startBtn.disabled = false;
    broadcastState();
  }, 70);
}

function endRound() {
  clearInterval(tickId);
  tickId = null;
  timerEl.textContent = 'Zeit!';
  timerEl.className = 'timer over';
  showWordsBtn.hidden = false;
  playAlarm();
  broadcastState();
}

// Vom Startbildschirm ins Spiel: Feld in der gewählten Größe aufbauen und gleich würfeln
function startGame() {
  buildBoard(boardSize);
  menuEl.hidden = true;
  gameEl.hidden = false;
  startRound();
}

function openMenu() {
  // Zuschauer verlassen die Sitzung und landen im eigenen Startbildschirm
  if (watching) {
    location.href = location.pathname;
    return;
  }
  if (tickId && !confirm('Laufende Runde abbrechen und zum Menü?')) return;
  clearInterval(tickId);
  clearInterval(shakeId);
  tickId = null;
  shakeId = null;
  roundId++;
  boardEl.classList.remove('shaking');
  startBtn.disabled = false;
  resultsEl.hidden = true;
  hideDefinition();
  gameEl.hidden = true;
  menuEl.hidden = false;
  broadcastState();
}

// --- Einstellungen ---------------------------------------------------------------

function showDuration() {
  minutesInput.value = Math.floor(roundSeconds / 60);
  secondsInput.value = String(roundSeconds % 60).padStart(2, '0');
}

// Eingabe übernehmen, auf gültigen Bereich begrenzen und merken
function readDuration() {
  const min = parseInt(minutesInput.value, 10) || 0;
  const sec = parseInt(secondsInput.value, 10) || 0;
  roundSeconds = Math.min(MAX_SECONDS, Math.max(MIN_SECONDS, min * 60 + sec));
  saveSetting(DURATION_KEY, roundSeconds);
}

function markSelected(groupEl, value) {
  for (const btn of groupEl.querySelectorAll('button')) {
    btn.setAttribute('aria-pressed', String(btn.dataset.value === String(value)));
  }
}

// Gilt ab dem nächsten "Spiel starten"
function setBoardSize(n) {
  boardSize = n;
  saveSetting(SIZE_KEY, n);
  markSelected(sizeOptionsEl, n);
}

function applyTheme(theme) {
  document.documentElement.dataset.theme = theme;
  themeColorMeta.content = getComputedStyle(document.documentElement).getPropertyValue('--bg').trim();
}

function setTheme(theme) {
  applyTheme(theme);
  saveSetting(THEME_KEY, theme);
  markSelected(themeOptionsEl, theme);
  broadcastState();
}

function initSettings() {
  const savedSeconds = parseInt(loadSetting(DURATION_KEY), 10);
  if (savedSeconds >= MIN_SECONDS && savedSeconds <= MAX_SECONDS) roundSeconds = savedSeconds;
  showDuration();

  for (const input of [minutesInput, secondsInput]) {
    input.addEventListener('input', readDuration);
    // Beim Verlassen des Feldes korrigierte Werte (z. B. 90 s → 1:30) anzeigen
    input.addEventListener('change', showDuration);
    input.addEventListener('keydown', (e) => { if (e.key === 'Enter') input.blur(); });
  }

  const savedSize = parseInt(loadSetting(SIZE_KEY), 10);
  setBoardSize(BOARD_SIZES.includes(savedSize) ? savedSize : 4);
  sizeOptionsEl.addEventListener('click', (e) => {
    const value = parseInt(e.target.closest('button')?.dataset.value, 10);
    if (value && value !== boardSize) setBoardSize(value);
  });

  const savedTheme = loadSetting(THEME_KEY);
  setTheme(THEMES.includes(savedTheme) ? savedTheme : 'classic');
  themeOptionsEl.addEventListener('click', (e) => {
    const value = e.target.closest('button')?.dataset.value;
    if (value) setTheme(value);
  });
}

// --- Längste Wörter ------------------------------------------------------------

// Wie bei Wortwürfelspielen üblich: Umlaute als AE/OE/UE, ß als SS
function boardForm(word) {
  return word.toUpperCase().replace(/Ä/g, 'AE').replace(/Ö/g, 'OE').replace(/Ü/g, 'UE').replace(/ß/g, 'SS');
}

// Wortliste "Wort<TAB>Häufigkeit" (Häufigkeit in Film-/Serienuntertiteln, für Fachwörter)
function loadDictionary() {
  dictionary ??= fetch('data/words.txt')
    .then((res) => {
      if (!res.ok) throw new Error(res.status);
      return res.text();
    })
    .then((text) => {
      const words = [];
      const counts = new Map();
      for (const line of text.split('\n')) {
        const [word, count] = line.split('\t');
        if (!word) continue;
        words.push(word);
        counts.set(word.toLowerCase(), Number(count) || 0);
      }
      return { words, counts };
    })
    .catch((err) => {
      dictionary = null;
      throw err;
    });
  return dictionary;
}

// Sucht einen Weg über benachbarte, unbenutzte Würfel; liefert die Feldindizes oder null
function findPath(tokens) {
  const used = new Array(letters.length).fill(false);
  const path = [];
  const visit = (cell, i) => {
    if (used[cell] || letters[cell] !== tokens[i]) return false;
    used[cell] = true;
    path.push(cell);
    if (i === tokens.length - 1) return true;
    for (const next of neighbors[cell]) {
      if (visit(next, i + 1)) return true;
    }
    used[cell] = false;
    path.pop();
    return false;
  };
  for (let cell = 0; cell < letters.length; cell++) {
    if (visit(cell, 0)) return path;
  }
  return null;
}

// Liefert die legbaren Wörter nach und nach, längste zuerst (die Wortliste ist so sortiert)
function* boardWords(words) {
  const available = {};
  for (const l of letters) available[l] = (available[l] || 0) + 1;

  for (const word of words) {
    const form = boardForm(word);
    const tokens = form.replace(/QU/g, 'Q').split('');
    if (tokens.length > letters.length) continue;
    const need = {};
    if (tokens.some((t) => (need[t] = (need[t] || 0) + 1) > (available[t] || 0))) continue;
    const path = findPath(tokens);
    if (path) yield { word, length: form.length, path };
  }
}

function take(iterator, n) {
  const out = [];
  while (out.length < n) {
    const next = iterator.next();
    if (next.done) break;
    out.push(next.value);
  }
  return out;
}

function renderWordList(found) {
  wordListEl.replaceChildren(...found.map(({ word, length, path }) => {
    const li = document.createElement('li');
    const btn = document.createElement('button');
    const w = document.createElement('span');
    w.className = 'word';
    w.textContent = word;
    const len = document.createElement('span');
    len.className = 'len';
    len.textContent = length;
    btn.append(w, len);
    btn.addEventListener('click', () => {
      const wasActive = btn.classList.contains('active');
      wordListEl.querySelectorAll('button').forEach((b) => b.classList.remove('active'));
      btn.classList.toggle('active', !wasActive);
      highlightPath(wasActive ? null : path);
      if (wasActive) hideDefinition();
      else showDefinition(word);
    });
    li.append(btn);
    return li;
  }));
}

// Behält nur Wörter mit sicherer Definition (keine nur vermutete Grundform) und einem Beispielsatz,
// in dem das Wort vorkommt, die außerdem keine reine Dativ-Plural-Form und weder englisch
// noch nur österreichisch/schweizerisch, seltene Fachsprache, Marke, seltener Eigenname,
// Kurzwort (außer eingebürgerten wie "Auto") noch als "attributiv"
// gekennzeichnet sind,
// in Längenreihenfolge, bis TOP_WORDS erreicht sind.
// Wirft einen Fehler, wenn gar nichts geprüft werden konnte (z. B. offline).
async function withDefinitions(candidates, round, counts) {
  // Fachwörter, die im Alltag häufig vorkommen (Computer, Atom, Aspirin), bleiben erlaubt
  const isCommon = (...forms) => forms.some((w) => w && (counts.get(w.toLowerCase()) || 0) >= COMMON_WORD_COUNT);
  const blocks = (restriction, word, title) => restriction && !(restriction === 'technical' && isCommon(word, title));
  const kept = [];
  let checked = 0;
  for (let total = 0; kept.length < TOP_WORDS && total < MAX_CHECKED_WORDS; total += LOOKUP_BATCH) {
    const batch = take(candidates, LOOKUP_BATCH);
    if (!batch.length) break;
    const results = await Promise.allSettled(batch.map((c) => getDefinition(c.word)));
    if (round !== roundId) return [];
    results.forEach((r, j) => {
      if (r.status !== 'fulfilled') return;
      checked++;
      const {
        title, meaning, example, guessed, dativePlural, english, restriction, attributive, properNoun, shortForm,
      } = r.value;
      const restricted = blocks(restriction, batch[j].word, title);
      // Seltene Wörter, die auch Eigenname sind ("Assam"); häufige wie "Essen" oder "Halle" bleiben
      const properName = properNoun && !isCommon(batch[j].word);
      const allowed = meaning && example && !guessed && !dativePlural && !english && !restricted
        && !properName && !attributive && !shortForm;
      if (allowed) {
        kept.push(batch[j]);
      }
    });
    if (!checked) throw new Error('Wiktionary nicht erreichbar');
    resultsStatusEl.textContent = `Definitionen werden geprüft … (${Math.min(kept.length, TOP_WORDS)}/${TOP_WORDS})`;
  }
  return kept.slice(0, TOP_WORDS);
}

async function showLongestWords() {
  const round = roundId;
  showWordsBtn.hidden = true;
  timerEl.hidden = true;
  resultsEl.hidden = false;
  wordListEl.replaceChildren();
  resultsStatusEl.textContent = 'Wörterbuch wird geladen …';
  let words;
  let counts;
  try {
    ({ words, counts } = await loadDictionary());
  } catch {
    resultsStatusEl.textContent = 'Das Wörterbuch konnte nicht geladen werden.';
    showWordsBtn.hidden = false;
    return;
  }
  if (round !== roundId) return;

  const iterator = boardWords(words);
  const firstWords = take(iterator, TOP_WORDS); // ungeprüfte Liste, falls offline
  const candidates = (function* () { yield* firstWords; yield* iterator; })();
  resultsStatusEl.textContent = 'Definitionen werden geprüft …';
  let found;
  let status;
  try {
    found = await withDefinitions(candidates, round, counts);
    status = found.length
      ? 'Tippe ein Wort an, um es auf dem Feld zu sehen.'
      : 'Auf diesem Feld wurde kein Wort mit Definition gefunden.';
  } catch {
    found = firstWords;
    status = 'Ohne Internet können die Wörter nicht auf eine Definition geprüft werden – die Liste ist ungefiltert.';
  }
  if (round !== roundId) return;
  resultsStatusEl.textContent = status;
  renderWordList(found);
  resultsEl.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
  lastResults = { words: found, status };
  broadcastState();
}

// --- Definitionen (aus dem deutschen Wiktionary, braucht Internet) -------------

const WIKTIONARY_API = 'https://de.wiktionary.org/w/api.php';
const MAX_DEFINITION_LENGTH = 220;

async function wiktionaryPages(titles, withContent) {
  const params = new URLSearchParams({
    action: 'query', format: 'json', formatversion: '2', origin: '*', titles: titles.join('|'),
  });
  if (withContent) {
    params.set('prop', 'revisions');
    params.set('rvprop', 'content');
    params.set('rvslots', 'main');
    params.set('redirects', '1');
  }
  const res = await fetch(`${WIKTIONARY_API}?${params}`);
  if (!res.ok) throw new Error(res.status);
  return (await res.json()).query?.pages || [];
}

// Wiki-Markup entfernen: Vorlagen, Links, Fettdruck, Einzelnachweise
function cleanWikitext(text) {
  let s = text
    .replace(/<!--[\s\S]*?-->/g, '')
    .replace(/<ref[^>]*\/>/g, '')
    .replace(/<ref[\s\S]*?<\/ref>/g, '')
    .replace(/<[^>]+>/g, '');
  let prev;
  do {
    prev = s;
    s = s.replace(/\{\{([^{}]*)\}\}/g, (_, inner) => {
      const [name, ...params] = inner.split('|').map((p) => p.trim());
      const positional = params.filter((p) => !/^[\w-]+=/.test(p));
      if (name === 'K') return positional.length ? `${positional.join(', ')}:` : '';
      if (/^(QS|Audio|Ref)/.test(name)) return '';
      if (!params.length) return name; // z. B. {{ugs.}}
      const last = positional[positional.length - 1] || '';
      return /^[;:,.]$/.test(last) ? name + last : last; // z. B. {{intrans.|;}}
    });
  } while (s !== prev);
  return s
    .replace(/\[\[(?:[^\]|]*\|)?([^\]]*)\]\]/g, '$1')
    .replace(/'{2,}/g, '')
    .replace(/^:\s*(\[[^\]]*\])?\s*/, '')
    .replace(/\s+/g, ' ')
    .trim();
}

function shorten(text) {
  return text.length > MAX_DEFINITION_LENGTH ? `${text.slice(0, MAX_DEFINITION_LENGTH).trim()} …` : text;
}

// Deutscher Teil einer Wiktionary-Seite, beginnt mit "== Wort ({{Sprache|Deutsch}}) =="
// (manche Seiten schreiben die Überschriften ohne Leerzeichen: "==asch ({{Sprache|Schwedisch}})==")
function germanPart(text) {
  return text.split(/^(?===[^=])/m).find((part) => /^==[^=\n]*\{\{Sprache\|Deutsch\}\}/.test(part)) || '';
}

// Wortart-Abschnitte des deutschen Teils, z. B. "=== {{Wortart|Substantiv|Deutsch}}, {{m}} ==="
function germanSections(german) {
  return german.split(/^(?====[^=])/m).slice(1).filter((s) => s.slice(0, s.indexOf('\n')).includes('Deutsch'));
}

// Eigennamen sind als Lösungswörter nicht erlaubt, deren Bedeutungen also überspringen
const SKIPPED_WORD_TYPES = /Toponym|Vorname|Nachname|Eigenname|Familienname|Abkürzung|Markenname|Warenzeichen/;

// Eingebürgerte Alltagswörter aus dem Englischen, die trotzdem gelten sollen (Grundformen, beliebig erweiterbar)
const ALLOWED_ENGLISH_WORDS = new Set([
  'Baby', 'Band', 'Bar', 'Boss', 'Bus', 'Camping', 'Clown', 'Comic', 'Computer', 'Cowboy', 'Fan', 'Film',
  'Golf', 'Hit', 'Hobby', 'Hockey', 'Internet', 'Interview', 'Jazz', 'Jeans', 'Job', 'Ketchup', 'Lift',
  'Manager', 'Partner', 'Party', 'Pony', 'Pop', 'Pullover', 'Rock', 'Sandwich', 'Shampoo', 'Shop',
  'Show', 'Smoking', 'Song', 'Sport', 'Star', 'Start', 'starten', 'Steak', 'Stress', 'Team', 'Tennis',
  'Taxi', 'Test', 'testen', 'Ticket', 'Toast', 'Trainer', 'Training', 'Trend',
].map((w) => w.toLowerCase()));

// Text des Abschnitts "Herkunft" eines Eintrags
function originText(section) {
  const lines = section.split('\n');
  const i = lines.findIndex((l) => l.trim() === '{{Herkunft}}');
  let origin = '';
  for (let j = i + 1; i >= 0 && j < lines.length && lines[j].startsWith(':'); j++) origin += lines[j];
  return origin;
}

// Unverändert aus dem Englischen übernommen? Erkennbar daran, dass die Herkunft mit dem
// gleich geschriebenen englischen Wort beginnt, z. B. "von englisch {{Ü|en|claim}} entlehnt".
// Eingedeutschte Wörter (Streik ← strike) und bloß verwandte (Butter, Wind) bleiben erlaubt.
function isEnglishLoan(section, title) {
  const origin = originText(section);
  const word = title.toLowerCase();
  if (ALLOWED_ENGLISH_WORDS.has(word)) return false;
  const same = (source) => source === word || source === `${word}s` || `${source}s` === word; // "Ranking" ← "rankings"
  const first = origin.match(/\{\{Ü\|([^|}]+)\|([^|}]+)/);
  if (first) return first[1] === 'en' && same(first[2].trim().toLowerCase());
  // Ohne Vorlage, nur als Text: "aus dem Englischen von ''call (option)''" (bei "Call")
  const text = cleanWikitext(origin).toLowerCase();
  const source = text.match(/(?:aus dem englischen|vom englischen|von (?:gleichbedeutend )?englisch|aus englisch)\s+(?:von\s+)?["„“']*([\p{L}]+)/u)?.[1];
  return Boolean(source) && same(source);
}

// Eingebürgerte Kurzwörter, deren Langform kaum noch jemand benutzt – gelten nicht als Abkürzung
// (Grundformen, beliebig erweiterbar)
const ALLOWED_SHORT_WORDS = new Set([
  'Auto', 'Bus', 'Deo', 'Disko', 'Foto', 'Kilo', 'Kino', 'Krimi', 'Labor', 'Lok', 'Tacho', 'Taxi', 'Zoo',
].map((w) => w.toLowerCase()));

const SHORT_FORM = /kurz für|Kurzwort|Kurzform|Kurzbezeichnung|Kopfwort|Schwanzwort|Akronym|Initialwort|gekürzt aus/i;

// Kurzwort wie "Soli" (kurz für Solidaritätszuschlag) oder "Abi" (Kurzwort zu Abitur)?
// Steht entweder in der Bedeutung selbst oder in der Herkunft.
function isShortForm(section, meaningLine) {
  return SHORT_FORM.test(cleanWikitext(meaningLine)) || SHORT_FORM.test(cleanWikitext(originText(section)));
}

// Österreichisch/schweizerisch, wenn die erste Regionsangabe einer Bedeutung AT/CH ist,
// z. B. "{{K|österr.}} Tomate" oder "{{K|Schweiz}} Speiseeis". Steht zuerst eine deutsche
// Region (z. B. "{{K|süddeutsch|österreichisch}}" bei "Bub"), bleibt das Wort erlaubt.
const AT_CH_REGION = /[öÖ]sterr|[sS]chweiz|Wien|Liechtenst|\bCH\b|\bAT\b/;
const GERMAN_REGION = /deutsch|\b(süd|nord|ost|west|mittel)\w*|bayr|bair|bayern|schwäb|landsch|sonst/i;

// Nur die Kennzeichnung am Zeilenanfang, nicht der Bedeutungstext, z. B. "{{K|österr.}}"
function meaningLabel(line) {
  return line.match(/^:\s*(?:\[[^\]]*\])?\s*((?:\{\{(?:[^{}]|\{\{[^{}]*\}\})*\}\}\s*|''[^']*''\s*)*)/)?.[1] || '';
}

// Als "attributiv" gekennzeichnete Bedeutung, z. B. "{{K|attributiv|prädikativ}}" bei "selten"
function isAttributive(line) {
  const label = meaningLabel(line);
  return /attributiv|\battr\./i.test(label) && !/nicht attr/i.test(label);
}

function isAustrianOrSwiss(line) {
  const label = meaningLabel(line);
  const atCh = label.search(AT_CH_REGION);
  if (atCh < 0) return false;
  const german = label.search(GERMAN_REGION);
  return german < 0 || atCh < german;
}

// Nummer einer Bedeutung bzw. eines Beispiels, z. B. "1" aus ":[1] …" oder "1, 2" aus ":[1, 2] …"
function meaningNumber(line) {
  return line.match(/^:\s*\[([^\]]*)\]/)?.[1].trim() || '';
}

// Alle Beispielsätze eines Abschnitts samt den Nummern der Bedeutungen, zu denen sie gehören
function examplesOf(lines) {
  const start = lines.findIndex((l) => l.trim() === '{{Beispiele}}');
  const examples = [];
  for (let j = start + 1; start >= 0 && j < lines.length && lines[j].startsWith(':'); j++) {
    if (lines[j].includes('{{Beispiele fehlen')) continue;
    const text = cleanWikitext(lines[j]);
    if (text.split(' ').length >= 3) examples.push({ numbers: meaningNumber(lines[j]).split(/\s*,\s*/), text });
  }
  return examples;
}

// Steht genau diese Wortform als ganzes Wort im Satz? ("Dorns" zählt nicht in "Dorn" oder "Dornstrauch")
function containsForm(text, form) {
  const escaped = form.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return new RegExp(`(^|[^\\p{L}])${escaped}(?![\\p{L}])`, 'iu').test(text);
}

// Kürzester Beispielsatz zu dieser Bedeutung, der genau die angezeigte Wortform enthält
// (lange Literaturzitate sind schwer lesbar)
function exampleWithForm(examples, number, form) {
  const hits = examples
    .filter((e) => e.numbers.includes(number) && containsForm(e.text, form))
    .map((e) => e.text)
    .sort((a, b) => a.length - b.length);
  return hits.length ? shorten(hits[0]) : '';
}

// Ist die Wortform ausschließlich Dativ Plural (z. B. "Heeren" von "Heer")? Steht im Eintrag unter
// "Grammatische Merkmale", z. B. "*Dativ Plural des Substantivs Heer". Hat das Wort eigene
// Bedeutungen oder noch andere Formen (z. B. "Seen" auch Nominativ Plural), bleibt es erlaubt.
function isOnlyDativePlural(german) {
  const features = [];
  for (const section of germanSections(german)) {
    if (SKIPPED_WORD_TYPES.test(section.slice(0, section.indexOf('\n')))) continue;
    if (section.includes('{{Bedeutungen}}')) return false;
    const lines = section.split('\n');
    const i = lines.findIndex((l) => l.trim() === '{{Grammatische Merkmale}}');
    for (let j = i + 1; i >= 0 && j < lines.length && lines[j].startsWith('*'); j++) features.push(lines[j]);
  }
  return features.length > 0 && features.every((f) => /^\*\s*Dativ Plural/.test(f));
}

// Fachgebiete, deren Wörter nicht zum allgemeinen Sprachgebrauch zählen (z. B. "Fossa": Anatomie,
// Zoologie). Alltagsnahe Gebiete wie Musik, Sport, Gastronomie oder Militär zählen bewusst nicht dazu.
const TECHNICAL_FIELDS = new RegExp([
  'fachspr', 'Fachjargon', 'Nomenklatur', 'Anatomie', 'anatomisch', 'Astronomie', 'Astrogeologie',
  'Astrophysik', 'Biochemie', 'Biologie', 'Botanik', 'Chemie', 'Elektrotechnik', 'Elektronik',
  'Entomologie', 'Ethnologie', 'Genetik', 'Geologie', 'Geometrie', 'Heraldik', 'Hüttenwesen',
  'Ichthyologie', 'Informatik', 'Kristallographie', 'Linguistik', 'Mathematik', 'Medizin', 'Metallurgie',
  'Meteorologie', 'Mineralogie', 'Mykologie', 'Nautik', 'Numismatik', 'Ornithologie', 'Paläontologie',
  'Pathologie', 'Pharmakologie', 'Pharmazie', 'Philosophie', 'Phonetik', 'Physik', 'Physiologie',
  'Psychologie', 'Rechtswesen', 'Soziologie', 'Statistik', 'Technik', 'Textilwesen', 'Theologie',
  'Typografie', 'Typographie', 'Zoologie', 'Bergbau', 'Bauwesen', 'Druckwesen', 'Jägersprache', 'Grammatik',
].join('|'), 'i');
const BRAND = /Marken(name|zeichen)|Warenzeichen|Handelsname/i;

// Warum eine Bedeutung nicht zählt: 'regional' (AT/CH), 'brand' (Marke), 'technical' (Fachsprache)
function meaningRestriction(line) {
  if (isAustrianOrSwiss(line)) return 'regional';
  const label = meaningLabel(line);
  if (BRAND.test(label)) return 'brand';
  if (TECHNICAL_FIELDS.test(label)) return 'technical';
  return null;
}

// Liefert die uneingeschränkten Bedeutungen des ersten passenden Abschnitts samt Beispielsätzen,
// sonst den Verweis auf die Grundform (oder eingeschränkte Bedeutungen samt Grund, damit das
// Wort aussortiert wird)
function parseEntry(text, title) {
  const german = germanPart(text);
  if (!german) return null;
  let lemma = null;
  let restricted = null;
  for (const section of germanSections(german)) {
    if (SKIPPED_WORD_TYPES.test(section.slice(0, section.indexOf('\n')))) continue;
    const lines = section.split('\n');
    const start = lines.findIndex((l) => l.trim() === '{{Bedeutungen}}');
    const senses = [];
    for (let j = start + 1; start >= 0 && j < lines.length && lines[j].startsWith(':'); j++) {
      const meaning = cleanWikitext(lines[j]);
      if (!meaning) continue;
      senses.push({
        number: meaningNumber(lines[j]),
        meaning: shorten(meaning),
        attributive: isAttributive(lines[j]),
        shortForm: isShortForm(section, lines[j]),
        restriction: meaningRestriction(lines[j]),
      });
    }
    if (senses.length) {
      const result = { senses, examples: examplesOf(lines), lemma: null, english: isEnglishLoan(section, title) };
      // Fachsprachliche Bedeutungen bleiben im Spiel: ob das Wort trotzdem alltäglich ist
      // (Auto, Computer), entscheidet später die Häufigkeit
      const open = senses.filter((s) => s.restriction !== 'regional' && s.restriction !== 'brand');
      if (open.length) return { ...result, senses: open, restriction: null };
      restricted ??= { ...result, restriction: senses[0].restriction };
    }
    // z. B. {{Grundformverweis Konj|Abschnitt=Verb|erlesen}} -> "erlesen"
    const ref = section.match(/\{\{Grundformverweis[^}]*\}\}/)?.[0];
    lemma ??= ref?.slice(2, -2).split('|').slice(1).map((p) => p.trim()).find((p) => p && !p.includes('=')) ?? null;
  }
  const dativePlural = isOnlyDativePlural(german);
  if (lemma) return { senses: [], lemma, dativePlural };
  return { ...(restricted ?? { senses: [], lemma: null }), dativePlural };
}

const hasMeaning = (entry) => entry?.senses?.length > 0;

// Hat der Eintrag auch einen Abschnitt als Eigenname (Ort, Name, Marke)? z. B. "Assam" (Bundesstaat)
function hasProperNounSection(text) {
  return germanSections(germanPart(text))
    .some((section) => SKIPPED_WORD_TYPES.test(section.slice(0, section.indexOf('\n'))));
}

async function fetchEntry(title) {
  const [page] = await wiktionaryPages([title], true);
  const text = page?.revisions?.[0]?.slots?.main?.content;
  return text ? { title: page.title, ...parseEntry(text, page.title), properNoun: hasProperNounSection(text) } : null;
}

// Typische deutsche Beugungsendungen, kürzeste zuerst ("nem" etc. für "erlesnem" -> "erlesen")
const INFLECTION_ENDINGS = [
  'e', 'n', 's', 't',
  'em', 'en', 'er', 'es', 'et', 'st', 'te', 'ne',
  'est', 'ste', 'ten', 'tet', 'ter', 'tes', 'tem', 'nde', 'nem', 'nen', 'ner', 'nes',
  'sten', 'ster', 'stes', 'stem', 'nden', 'ndem', 'nder', 'ndes',
];

// Mögliche Grundformen für Wörter ohne eigenen Eintrag
function stemCandidates(word) {
  const out = [];
  for (const ending of INFLECTION_ENDINGS) {
    if (!word.endsWith(ending) || word.length - ending.length < 3) continue;
    const stem = word.slice(0, -ending.length);
    out.push(stem, `${stem}e`, `${stem}en`, `${stem}n`);
  }
  return [...new Set(out)].filter((c) => c !== word);
}

async function lookupDefinition(word) {
  let entry = await fetchEntry(word);
  const dativePlural = entry?.dativePlural ?? false; // gilt für die Wortform selbst, nicht die Grundform
  const ownEntry = entry;
  let guessed = false;
  if (!hasMeaning(entry) && !entry?.lemma) {
    const candidates = stemCandidates(word);
    const existing = candidates.length
      ? new Set((await wiktionaryPages(candidates, false)).filter((p) => !p.missing).map((p) => p.title))
      : new Set();
    const stem = candidates.find((c) => existing.has(c));
    if (stem) {
      entry = await fetchEntry(stem);
      guessed = true;
    }
  }
  // Gebeugte Formen verweisen auf ihre Grundform (teils über mehrere Stufen)
  for (let depth = 0; entry && !hasMeaning(entry) && entry.lemma && depth < 3; depth++) {
    entry = await fetchEntry(entry.lemma);
  }
  if (!hasMeaning(entry)) return { title: null, meaning: null, guessed: false };

  // Erste Bedeutung, zu der es einen Beispielsatz mit genau dieser Wortform gibt ("Dorns", nicht "Dorn");
  // allgemeine Bedeutungen vor fachsprachlichen
  const senses = entry.senses.map((s) => ({ ...s, example: exampleWithForm(entry.examples, s.number, word) }));
  const ordered = [...senses.filter((s) => !s.restriction), ...senses.filter((s) => s.restriction)];
  const sense = ordered.find((s) => s.example) ?? ordered[0];
  return {
    title: entry.title,
    meaning: sense.meaning,
    example: sense.example,
    guessed,
    dativePlural,
    // Bedeutung stammt aus einem Eintrag, der auch Eigenname ist ("Assam"); "Sitten" -> "Sitte" zählt nicht
    properNoun: entry === ownEntry && entry.properNoun,
    english: entry.english,
    restriction: sense.restriction ?? entry.restriction,
    shortForm: sense.shortForm && !ALLOWED_SHORT_WORDS.has(entry.title.toLowerCase()),
    attributive: sense.attributive,
  };
}

// Zwischengespeichert, damit die Prüfung der Liste und das Antippen nur einmal abfragen
function getDefinition(word) {
  if (!definitions.has(word)) {
    definitions.set(word, lookupDefinition(word).catch((err) => {
      definitions.delete(word);
      throw err;
    }));
  }
  return definitions.get(word);
}

function wiktionaryUrl(title) {
  return `https://de.wiktionary.org/wiki/${encodeURIComponent(title)}`;
}

// Duden-Suche statt direkter Seite: findet auch Wörter mit mehreren Einträgen (z. B. "Tempo")
function dudenUrl(title) {
  return `https://www.duden.de/suchen/dudenonline/${encodeURIComponent(title)}`;
}

async function showDefinition(word) {
  const request = ++definitionRequest;
  definitionEl.hidden = false;
  defWordEl.textContent = word;
  defTextEl.textContent = 'Definition wird geladen …';
  defExampleEl.hidden = true;
  defLinksEl.hidden = true;

  try {
    const { title, meaning, example, guessed } = await getDefinition(word);
    if (request !== definitionRequest) return;
    defWordEl.textContent = title && title !== word
      ? `${word} → ${title}${guessed ? ' (vermutet)' : ''}`
      : word;
    defTextEl.textContent = meaning || 'Keine Definition gefunden.';
    if (meaning) {
      defExampleEl.textContent = example || 'Kein Beispielsatz vorhanden.';
      defExampleEl.classList.toggle('missing', !example);
      defExampleEl.hidden = false;
    }
    defLinkEl.href = wiktionaryUrl(title || word);
    defDudenEl.href = dudenUrl(title || word);
    defLinksEl.hidden = false;
  } catch {
    if (request !== definitionRequest) return;
    defTextEl.textContent = navigator.onLine
      ? 'Die Definition konnte nicht geladen werden.'
      : 'Für Definitionen wird eine Internetverbindung benötigt.';
  }
  definitionEl.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
}

function hideDefinition() {
  definitionRequest++;
  definitionEl.hidden = true;
}

// --- Ton -------------------------------------------------------------------

// Browser erlauben Audio erst nach einer Berührung, daher beim Start freischalten
function unlockAudio() {
  const Ctx = window.AudioContext || window.webkitAudioContext;
  if (!Ctx) return;
  if (!audioCtx) audioCtx = new Ctx();
  if (audioCtx.state === 'suspended') audioCtx.resume();
  const src = audioCtx.createBufferSource();
  src.buffer = audioCtx.createBuffer(1, 1, 22050);
  src.connect(audioCtx.destination);
  src.start(0);
}

function beep(at, freq, duration) {
  const osc = audioCtx.createOscillator();
  const gain = audioCtx.createGain();
  osc.type = 'square';
  osc.frequency.value = freq;
  gain.gain.setValueAtTime(0.0001, at);
  gain.gain.exponentialRampToValueAtTime(0.35, at + 0.01);
  gain.gain.exponentialRampToValueAtTime(0.0001, at + duration);
  osc.connect(gain).connect(audioCtx.destination);
  osc.start(at);
  osc.stop(at + duration + 0.05);
}

function playAlarm() {
  if (!audioCtx) return;
  if (audioCtx.state === 'suspended') audioCtx.resume();
  const t = audioCtx.currentTime + 0.05;
  beep(t, 880, 0.2);
  beep(t + 0.3, 880, 0.2);
  beep(t + 0.6, 880, 0.2);
  beep(t + 0.9, 660, 0.8);
}

// --- Bildschirm anlassen -----------------------------------------------------

async function requestWakeLock() {
  if (!('wakeLock' in navigator) || wakeLock) return;
  try {
    wakeLock = await navigator.wakeLock.request('screen');
    wakeLock.addEventListener('release', () => { wakeLock = null; });
  } catch {
    // z. B. Energiesparmodus – dann eben ohne
  }
}

// Wake Lock geht verloren, wenn die App in den Hintergrund wechselt
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState !== 'visible' || !started) return;
  requestWakeLock();
  if (tickId) tick();
});

// --- Live-Sitzung: Zuschauer per Einladungslink -------------------------------
// Gastgeber und Zuschauer verbinden sich direkt (WebRTC) über die Bibliothek PeerJS. Deren
// kostenloser Vermittlungsdienst stellt nur den ersten Kontakt her; die Spieldaten gehen direkt
// von Gerät zu Gerät. PeerJS wird erst geladen, wenn jemand einlädt oder zuschaut.

const PEERJS_URL = 'https://cdnjs.cloudflare.com/ajax/libs/peerjs/1.5.4/peerjs.min.js';
const PEER_PREFIX = 'raschel-';
const JOIN_TIMEOUT_MS = 20000;

const inviteEl = document.getElementById('invite');
const inviteStatusEl = document.getElementById('invite-status');
const inviteLinkEl = document.getElementById('invite-link');
const inviteShareBtn = document.getElementById('invite-share');
const inviteCopyBtn = document.getElementById('invite-copy');
const inviteViewersEl = document.getElementById('invite-viewers');
const joinEl = document.getElementById('join');
const joinBtn = document.getElementById('join-btn');
const joinStatusEl = document.getElementById('join-status');
const liveBadgeEl = document.getElementById('live-badge');
const watchStatusEl = document.getElementById('watch-status');

let hostPeer = null;       // Promise<Peer> des Gastgebers, bleibt für die ganze Sitzung bestehen
let viewers = [];          // offene Verbindungen zu Zuschauern
let watching = false;      // dieses Gerät schaut nur zu
let shownResultsKey = '';  // welche Wortliste der Zuschauer gerade sieht (Feld + Wörter)

function loadPeerJs() {
  if (window.Peer) return Promise.resolve();
  return new Promise((resolve, reject) => {
    const script = document.createElement('script');
    script.src = PEERJS_URL;
    script.onload = resolve;
    script.onerror = () => reject(new Error('PeerJS konnte nicht geladen werden'));
    document.head.append(script);
  });
}

function randomId() {
  const bytes = crypto.getRandomValues(new Uint8Array(9));
  return Array.from(bytes, (b) => (b % 36).toString(36)).join('');
}

// Alles, was ein Zuschauer zum Anzeigen braucht. Restzeit statt Endzeitpunkt, damit
// unterschiedlich gestellte Uhren keine Rolle spielen.
function sessionState() {
  let phase = 'over';
  if (gameEl.hidden) phase = 'menu';
  else if (shakeId) phase = 'rolling';
  else if (tickId) phase = 'running';
  return {
    type: 'state',
    version: APP_VERSION,
    phase,
    size: boardSize,
    theme: document.documentElement.dataset.theme,
    letters,
    remainingMs: tickId ? Math.max(0, endTime - Date.now()) : 0,
    results: lastResults,
  };
}

function broadcastState() {
  if (!viewers.length) return;
  const state = sessionState();
  for (const conn of viewers) if (conn.open) conn.send(state);
}

// --- Gastgeber ---

function updateViewerCount() {
  const n = viewers.length;
  inviteViewersEl.textContent = n === 1 ? '1 Zuschauer verbunden' : `${n} Zuschauer verbunden`;
  document.getElementById('invite-btn').textContent = n ? `Einladen (${n})` : 'Einladen';
}

function ensureHostPeer() {
  hostPeer ??= loadPeerJs().then(() => new Promise((resolve, reject) => {
    const peer = new window.Peer(PEER_PREFIX + randomId());
    peer.on('open', () => resolve(peer));
    peer.on('error', (err) => reject(err));
    peer.on('connection', (conn) => {
      conn.on('open', () => {
        viewers.push(conn);
        conn.send(sessionState());
        updateViewerCount();
      });
      conn.on('close', () => {
        viewers = viewers.filter((c) => c !== conn);
        updateViewerCount();
      });
    });
    // Verbindung zum Vermittlungsdienst verloren: bestehende Zuschauer bleiben verbunden,
    // für neue Zuschauer wieder anmelden
    peer.on('disconnected', () => peer.reconnect());
  })).catch((err) => {
    hostPeer = null;
    throw err;
  });
  return hostPeer;
}

function inviteLink(peerId) {
  return `${location.origin}${location.pathname}?watch=${encodeURIComponent(peerId)}`;
}

async function openInvite() {
  inviteEl.hidden = false;
  inviteLinkEl.value = '';
  inviteShareBtn.disabled = true;
  inviteCopyBtn.disabled = true;
  inviteShareBtn.hidden = !navigator.share;
  inviteStatusEl.textContent = 'Einladungslink wird erstellt …';
  updateViewerCount();
  try {
    const peer = await ensureHostPeer();
    inviteLinkEl.value = inviteLink(peer.id);
    inviteStatusEl.textContent = 'Wer diesen Link öffnet, sieht deine Runden live mit. Lass die App dafür geöffnet.';
    inviteShareBtn.disabled = false;
    inviteCopyBtn.disabled = false;
  } catch {
    inviteStatusEl.textContent = navigator.onLine
      ? 'Der Vermittlungsdienst ist gerade nicht erreichbar. Bitte später noch einmal versuchen.'
      : 'Zum Einladen wird eine Internetverbindung benötigt.';
  }
}

async function shareInvite() {
  try {
    await navigator.share({ title: 'Raschel', text: 'Schau bei meiner Raschel-Runde zu:', url: inviteLinkEl.value });
  } catch { /* Teilen abgebrochen */ }
}

async function copyInvite() {
  try {
    await navigator.clipboard.writeText(inviteLinkEl.value);
    inviteCopyBtn.textContent = 'Kopiert ✓';
  } catch {
    // Ohne Zwischenablage-Zugriff: Link markieren, damit er von Hand kopiert werden kann
    inviteLinkEl.select();
    inviteCopyBtn.textContent = 'Markiert';
  }
  setTimeout(() => { inviteCopyBtn.textContent = 'Kopieren'; }, 2000);
}

// --- Zuschauer ---

function showWatchStatus(text) {
  watchStatusEl.textContent = text;
  watchStatusEl.hidden = !text;
}

// Gastgeber und Zuschauer sollten dieselbe Version nutzen, sonst kann die Anzeige abweichen
const versionNoticeEl = document.createElement('p');
versionNoticeEl.className = 'watch-status version-notice';
versionNoticeEl.hidden = true;
watchStatusEl.after(versionNoticeEl);

function checkHostVersion(hostVersion) {
  const mismatch = hostVersion !== undefined && hostVersion !== APP_VERSION;
  versionNoticeEl.hidden = !mismatch;
  if (!mismatch || versionNoticeEl.childElementCount) return;
  const reload = document.createElement('button');
  reload.type = 'button';
  reload.className = 'link-btn';
  reload.textContent = 'Neu laden';
  reload.addEventListener('click', () => location.reload());
  versionNoticeEl.append(`Der Gastgeber nutzt Version ${hostVersion}, du Version ${APP_VERSION}. `, reload);
}

function setLive(online) {
  liveBadgeEl.textContent = online ? 'Live' : 'Getrennt';
  liveBadgeEl.classList.toggle('offline', !online);
}

// Vom Gastgeber empfangenen Stand anzeigen
function applySessionState(state) {
  if (state?.type !== 'state') return;
  checkHostVersion(state.version);
  joinEl.hidden = true;
  menuEl.hidden = true;
  gameEl.hidden = false;
  applyTheme(state.theme);

  if (state.phase === 'menu' || !state.letters?.length) {
    clearInterval(tickId);
    tickId = null;
    timerEl.hidden = true;
    resultsEl.hidden = true;
    showWatchStatus('Warten auf die nächste Runde …');
    return;
  }
  showWatchStatus('');

  if (dieEls.length !== state.size * state.size) {
    boardSize = state.size;
    buildBoard(state.size);
  }
  const newBoard = state.letters.join() !== letters.join();
  letters = state.letters;
  renderBoard(letters);
  if (newBoard) {
    // Neue Runde: Liste, Markierung und Definition der vorigen Runde verwerfen
    highlightPath(null);
    hideDefinition();
    wordListEl.replaceChildren();
    shownResultsKey = '';
  }

  if (state.phase === 'running' || state.phase === 'rolling') {
    clearInterval(tickId);
    resultsEl.hidden = true;
    timerEl.hidden = false;
    timerEl.className = 'timer';
    endTime = Date.now() + state.remainingMs;
    tickId = setInterval(tick, 250);
    tick();
  } else if (state.phase === 'over') {
    // Läuft die eigene Uhr noch (hängt knapp hinterher), jetzt beenden – samt Alarm, aber nur einmal
    if (tickId) endRound();
    else if (!state.results) {
      timerEl.hidden = false;
      timerEl.textContent = 'Zeit!';
      timerEl.className = 'timer over';
    }
  }

  if (state.results) {
    timerEl.hidden = true;
    resultsEl.hidden = false;
    resultsStatusEl.textContent = state.results.status;
    // Nur neu zeichnen, wenn sich die Liste geändert hat – sonst ginge die Auswahl des Zuschauers verloren
    const key = `${letters.join('')}|${state.results.words.map((w) => w.word).join(',')}`;
    if (key !== shownResultsKey) {
      shownResultsKey = key;
      highlightPath(null);
      hideDefinition();
      renderWordList(state.results.words);
    }
  }
}

async function joinSession(hostId) {
  // Die Berührung auf "Zuschauen" erlaubt Ton und Bildschirm-anlassen
  unlockAudio();
  requestWakeLock();
  started = true;
  joinBtn.disabled = true;
  joinStatusEl.textContent = 'Verbinde …';

  const fail = (text) => {
    joinStatusEl.textContent = text;
    joinBtn.disabled = false;
    joinBtn.textContent = 'Erneut versuchen';
  };
  try {
    await loadPeerJs();
  } catch {
    fail(navigator.onLine ? 'Die Verbindung konnte nicht aufgebaut werden.' : 'Zum Zuschauen wird eine Internetverbindung benötigt.');
    return;
  }

  const peer = new window.Peer();
  let connected = false;
  const timeout = setTimeout(() => {
    if (connected) return;
    peer.destroy();
    fail('Keine Verbindung zum Gastgeber. Ist die App dort noch geöffnet?');
  }, JOIN_TIMEOUT_MS);

  peer.on('error', (err) => {
    if (connected) return;
    clearTimeout(timeout);
    peer.destroy();
    fail(err.type === 'peer-unavailable'
      ? 'Diese Sitzung gibt es nicht mehr. Bitte um einen neuen Einladungslink.'
      : 'Die Verbindung konnte nicht aufgebaut werden.');
  });
  peer.on('open', () => {
    const conn = peer.connect(hostId, { reliable: true });
    conn.on('open', () => {
      connected = true;
      clearTimeout(timeout);
      joinStatusEl.textContent = '';
      setLive(true);
    });
    conn.on('data', applySessionState);
    conn.on('close', () => {
      setLive(false);
      clearInterval(tickId);
      tickId = null;
      showWatchStatus('Die Verbindung zum Gastgeber wurde getrennt.');
    });
  });
}

function initWatchMode() {
  const hostId = new URLSearchParams(location.search).get('watch');
  if (!hostId || !hostId.startsWith(PEER_PREFIX)) return false;
  watching = true;
  document.body.classList.add('watching');
  menuBtn.textContent = '‹ Verlassen';
  liveBadgeEl.hidden = false;
  setLive(false);
  menuEl.hidden = true;
  joinEl.hidden = false;
  joinBtn.addEventListener('click', () => joinSession(hostId));
  return true;
}

// --- Start -------------------------------------------------------------------

document.getElementById('version').textContent = `v${APP_VERSION}`;
playBtn.addEventListener('click', startGame);
menuBtn.addEventListener('click', openMenu);
startBtn.addEventListener('click', startRound);
showWordsBtn.addEventListener('click', showLongestWords);
document.getElementById('invite-btn').addEventListener('click', openInvite);
document.getElementById('menu-invite').addEventListener('click', openInvite);
document.getElementById('invite-close').addEventListener('click', () => { inviteEl.hidden = true; });
inviteEl.addEventListener('click', (e) => { if (e.target === inviteEl) inviteEl.hidden = true; });
inviteShareBtn.addEventListener('click', shareInvite);
inviteCopyBtn.addEventListener('click', copyInvite);
initSettings();
initWatchMode();

if ('serviceWorker' in navigator) {
  // updateViaCache: 'none' – Änderungen an sw.js und version.js sofort erkennen
  navigator.serviceWorker.register('sw.js', { updateViaCache: 'none' });
}
