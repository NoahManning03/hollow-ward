'use strict';
(function () {
const $ = id => document.getElementById(id);
const TILE = 3, WALL_H = 3.6, EYE = 1.66, MAX_ALIVE = 24;

// ---------------------------------------------------------------- map state
// A map is one or more stacked tile layers (floors). Most maps have a single layer; towers add more, joined by stairs.
let MAP = [['#']], LAYERS = [MAP], NL = 1, W = 1, H = 1, DOORS = {}, THEME = null, MAPID = 'ward', bldF = null, navBlock = new Uint8Array(1), EVAC = null;
const FH = WALL_H, EVAC_WAVE = 5, EVAC_TIME = 60;
const COST = { crate: 950, ammo: 500, stim: 2500 };
const doorOpen = {}, doorMesh = {};
const SOLID = { '#': 1, B: 1, T: 1, R: 1, J: 1, W: 1, p: 1, x: 1, ' ': 1 }, OPEN = { '.': 1, ',': 1, '=': 1 }, HARD = { '#': 1, B: 1, R: 1 }, STAIR = { 1: 1, 2: 1, 3: 1, 4: 1 };
const N4 = [[1, 0], [-1, 0], [0, 1], [0, -1]];
const isDoor = ch => ch >= 'a' && ch <= 'f';
const tileL = (l, c, r) => { const g = LAYERS[l]; return (!g || c < 0 || r < 0 || c >= W || r >= H) ? '#' : g[r][c]; };
const tileAt = (c, r) => tileL(0, c, r);
function solidL(l, c, r) {
  const ch = tileL(l, c, r);
  if (SOLID[ch]) return true;
  if (l === 0 && DOORS[ch] && !doorOpen[ch]) return true;
  return false;
}
const solid = (c, r) => solidL(0, c, r);
const nidx = (l, c, r) => (l * H + r) * W + c;
// zombies also path around big props (cars, crate, stations) that sit in an otherwise open tile
const navSolidL = (l, c, r) => { if (solidL(l, c, r) || navBlock[nidx(l, c, r)] === 1) return true; if (NL === 1) return false; const ch = tileL(l, c, r); return STAIR[ch] === 1 || ch === 'v'; };
// Stairs: '1','2' = lower/upper half rising east, '3','4' = lower/upper half rising west. On the floor above, 'x' is the open
// stairwell over the lower half and 'v' is the opening over the upper half, which is where you step down from the landing.
function solidFor(e, c, r) {
  const l = e.l || 0; if (NL === 1) return solidL(0, c, r);
  const ec = Math.floor(e.x / TILE), er = Math.floor(e.z / TILE); if (c === ec && r === er) return false;
  const eh = tileL(l, ec, er);
  if (eh === '2' && c === ec + 1 && r === er) return solidL(l + 1, c, r);
  if (eh === '4' && c === ec - 1 && r === er) return solidL(l + 1, c, r);
  const ch = tileL(l, c, r);
  if (ch === '1') return !(r === er && (ec === c - 1 || eh === '2'));
  if (ch === '3') return !(r === er && (ec === c + 1 || eh === '4'));
  if (ch === '2') return !(r === er && eh === '1');
  if (ch === '4') return !(r === er && eh === '3');
  if (ch === 'v') return false;
  return solidL(l, c, r);
}
function relevel(e, pc, pr) {   // call after the centre of e may have crossed into another tile
  const l = e.l || 0, c = Math.floor(e.x / TILE), r = Math.floor(e.z / TILE); if (c === pc && r === pr) return;
  const ph = tileL(l, pc, pr);
  if ((ph === '2' && c === pc + 1 && r === pr) || (ph === '4' && c === pc - 1 && r === pr)) { e.l = l + 1; return; }
  if (tileL(l, c, r) === 'v' && l > 0) e.l = l - 1;
}
function groundY(e) {
  const l = e.l || 0; if (NL === 1) return 0;
  const c = Math.floor(e.x / TILE), ch = tileL(l, c, Math.floor(e.z / TILE)), fx = e.x / TILE - c, h = FH / 2;
  return l * FH + (ch === '1' ? fx * h : ch === '2' ? h + fx * h : ch === '3' ? (1 - fx) * h : ch === '4' ? h + (1 - fx) * h : 0);
}
// one pathfinding step from tile (l,c,r) in direction (dc,dr): returns the layer you end up on, or -1 if blocked
function navStep(l, c, r, dc, dr) {
  const nc = c + dc, nr = r + dr; if (NL === 1) return navSolidL(0, nc, nr) ? -1 : 0;
  const ch = tileL(l, c, r);
  if (ch === '2' && dc === 1 && !dr) return solidL(l + 1, nc, nr) ? -1 : l + 1;
  if (ch === '4' && dc === -1 && !dr) return solidL(l + 1, nc, nr) ? -1 : l + 1;
  if (STAIR[ch] && dr) return -1;
  const nh = tileL(l, nc, nr);
  if (nh === 'v') return l > 0 ? l - 1 : -1;
  if (nh === '1') return !dr && (dc === 1 || ch === '2') ? l : -1;
  if (nh === '3') return !dr && (dc === -1 || ch === '4') ? l : -1;
  if (nh === '2') return ch === '1' ? l : -1;
  if (nh === '4') return ch === '3' ? l : -1;
  return navSolidL(l, nc, nr) ? -1 : l;
}
const wx = c => c * TILE + TILE / 2;
let SPAWN = { x: 0, z: 0 };
const zSpawns = [], interactables = [], colliders = [];

// ---------------------------------------------------------------- weapons
const WEAPONS = {
  pistol:  { name: 'P9 Sidearm',    dmg: 38,  rpm: 420, auto: false, mag: 12,  reserve: 108, spread: .008, reload: 1.3, pellets: 1, kick: .030, zoom: 1.25 },
  smg:     { name: 'Viper SMG',     dmg: 30,  rpm: 850, auto: true,  mag: 32,  reserve: 224, spread: .022, reload: 1.9, pellets: 1, kick: .014, zoom: 1.3 },
  shotgun: { name: 'Breacher 12',   dmg: 34,  rpm: 80,  auto: false, mag: 6,   reserve: 48,  spread: .075, reload: 2.6, pellets: 8, kick: .085, zoom: 1.15 },
  rifle:   { name: 'Warden AR',     dmg: 48,  rpm: 620, auto: true,  mag: 30,  reserve: 240, spread: .012, reload: 2.2, pellets: 1, kick: .020, zoom: 1.5 },
  dmr:     { name: 'Longshot .308', dmg: 190, rpm: 150, auto: false, mag: 10,  reserve: 70,  spread: .002, reload: 2.6, pellets: 1, kick: .065, zoom: 2.6 },
  lmg:     { name: 'Hammer LMG',    dmg: 55,  rpm: 680, auto: true,  mag: 100, reserve: 300, spread: .020, reload: 4.2, pellets: 1, kick: .018, zoom: 1.3 },
  // Cold War era additions
  revolver: { name: 'Judge .357',     dmg: 150, rpm: 170,  auto: false, mag: 6,  reserve: 72,  spread: .004, reload: 2.4, pellets: 1,  kick: .075, zoom: 1.3,  snd: 'dmr' },
  mac:      { name: 'Stinger MP',     dmg: 24,  rpm: 1100, auto: true,  mag: 30, reserve: 270, spread: .030, reload: 1.6, pellets: 1,  kick: .012, zoom: 1.2,  snd: 'smg' },
  mp5:      { name: 'Kobra-5',        dmg: 34,  rpm: 780,  auto: true,  mag: 30, reserve: 240, spread: .016, reload: 1.9, pellets: 1,  kick: .013, zoom: 1.35, snd: 'smg' },
  ak:       { name: 'Kessler 47',     dmg: 62,  rpm: 560,  auto: true,  mag: 30, reserve: 210, spread: .015, reload: 2.4, pellets: 1,  kick: .028, zoom: 1.45, snd: 'rifle' },
  m16:      { name: 'Sentinel 16',    dmg: 56,  rpm: 900,  auto: false, mag: 30, reserve: 240, spread: .008, reload: 2.1, pellets: 1,  kick: .016, zoom: 1.6,  snd: 'rifle', burst: 3 },
  bullpup:  { name: 'Mistral B-1',    dmg: 44,  rpm: 920,  auto: true,  mag: 30, reserve: 240, spread: .014, reload: 2.3, pellets: 1,  kick: .017, zoom: 1.5,  snd: 'rifle' },
  autoshot: { name: 'Gravedigger-12', dmg: 30,  rpm: 230,  auto: false, mag: 8,  reserve: 56,  spread: .085, reload: 3.0, pellets: 8,  kick: .070, zoom: 1.15, snd: 'shotgun' },
  dbl:      { name: 'Twin Fang',      dmg: 48,  rpm: 200,  auto: false, mag: 2,  reserve: 40,  spread: .100, reload: 2.2, pellets: 10, kick: .120, zoom: 1.1,  snd: 'shotgun' },
  sniper:   { name: 'Glacier .50',    dmg: 700, rpm: 48,   auto: false, mag: 5,  reserve: 40,  spread: .0005, reload: 3.2, pellets: 1, kick: .100, zoom: 4,    snd: 'dmr' },
  autopistol: { name: 'Wasp M9',      dmg: 30,  rpm: 950,  auto: true,  mag: 20,  reserve: 200, spread: .016, reload: 1.5, pellets: 1, kick: .016, zoom: 1.25, snd: 'pistol', base: 'pistol' },
  handcannon: { name: 'Marshal .50',  dmg: 120, rpm: 240,  auto: false, mag: 7,   reserve: 70,  spread: .003, reload: 1.7, pellets: 1, kick: .070, zoom: 1.3,  snd: 'dmr', base: 'pistol' },
  lever:      { name: 'Ranger Lever', dmg: 140, rpm: 110,  auto: false, mag: 8,   reserve: 72,  spread: .002, reload: 2.8, pellets: 1, kick: .060, zoom: 1.8,  snd: 'dmr' },
  pdw:        { name: 'Hornet PDW',   dmg: 28,  rpm: 1000, auto: true,  mag: 40,  reserve: 280, spread: .014, reload: 1.8, pellets: 1, kick: .011, zoom: 1.3,  snd: 'smg' },
  battle:     { name: 'Harrier BR',   dmg: 98,  rpm: 330,  auto: false, mag: 20,  reserve: 160, spread: .002, reload: 2.4, pellets: 1, kick: .040, zoom: 2,    snd: 'rifle' },
  carbine:    { name: 'Whisper SD',   dmg: 50,  rpm: 700,  auto: true,  mag: 30,  reserve: 240, spread: .006, reload: 2.0, pellets: 1, kick: .012, zoom: 1.6,  snd: 'smg' },
  hmg:        { name: 'Anvil HMG',    dmg: 80,  rpm: 460,  auto: true,  mag: 75,  reserve: 225, spread: .012, reload: 4.6, pellets: 1, kick: .030, zoom: 1.4,  snd: 'lmg' },
  minigun:    { name: 'Cyclone',      dmg: 30,  rpm: 1500, auto: true,  mag: 200, reserve: 400, spread: .020, reload: 5.0, pellets: 1, kick: .008, zoom: 1.15, snd: 'lmg' },
  launcher:   { name: 'Thumper GL',   dmg: 420, rpm: 60,   auto: false, mag: 4,   reserve: 24,  spread: .002, reload: 3.2, pellets: 1, kick: .110, zoom: 1.3,  snd: 'shotgun', splash: 4.5 }
};
// guns sold from wall racks (half price buys ammo for one you already carry); the workbench upgrades the gun in your hands
const WCOST = { autopistol: 700, revolver: 900, mac: 900, smg: 1000, dbl: 1000, shotgun: 1200, mp5: 1200, pdw: 1300, lever: 1400, rifle: 1600, m16: 1600, carbine: 1700, ak: 1800 }, UP_COST = 3000;
const magOf = w => Math.round(WEAPONS[w.id].mag * (w.up ? 1.5 : 1)), resOf = w => Math.round(WEAPONS[w.id].reserve * (w.up ? 1.5 : 1)), dmgOf = w => WEAPONS[w.id].dmg * (w.up ? 1.75 : 1);
const wName = w => WEAPONS[w.id].name + (w.up ? ' Mk II' : '');
const aboxes = [];
// outfits: picked on the menu, sent to the host, and worn by your character in everyone else's game
const SKINS = [
  { name: 'Soldier',    cloth: 0x4a5a3c, pants: 0x33373a, vest: 0x2f3528, head: 0x3a4630, hat: 'helmet' },
  { name: 'Medic',      cloth: 0xc8c8c0, pants: 0x2a3a5a, vest: 0x9a2a26, head: 0xc8c8c0, hat: 'cap' },
  { name: 'Hazmat',     cloth: 0xb89a20, pants: 0xb89a20, vest: 0x55524a, head: 0xb89a20, hat: 'hood' },
  { name: 'Riot Cop',   cloth: 0x1c2538, pants: 0x161a24, vest: 0x0e1016, head: 0x12151c, hat: 'riot' },
  { name: 'Mercenary',  cloth: 0x1a1a1a, pants: 0x2a2620, vest: 0x3a3226, head: 0x101010, hat: 'mask' },
  { name: 'Woodsman',   cloth: 0x7a2a22, pants: 0x2a3448, vest: 0x4a3626, head: 0x30302e, hat: 'beanie' },
  { name: 'Inmate',     cloth: 0xc05a18, pants: 0xc05a18, vest: 0x6a6a66, head: 0x000000, hat: 'bare' },
  { name: 'Winter Ops', cloth: 0xd0d4d8, pants: 0xa8adb2, vest: 0x8a9096, head: 0xe0e2e4, hat: 'helmet' }
];
function skinOf(i) { const S = SKINS[i | 0] || SKINS[0]; if (!S.m) { S.m = {}; for (const k of ['cloth', 'pants', 'vest', 'head']) { S.m[k] = new THREE.MeshStandardMaterial({ color: S[k], roughness: .88 }); S.m[k].color.convertSRGBToLinear(); } } return S; }

// ---------------------------------------------------------------- state
let scene, camera, renderer, wscene, wcam, clock, raycaster;
const G = { started: false, host: true, myId: 'h', round: 0, state: 'inter', interT: 6, toSpawn: 0, spawnT: 0, insta: 0, evacT: 0, oi: 0, op: 0, og: 0, om: 0, time: 0, over: false, code: '' };
const players = {}; let me = null;
const zombies = [], zById = {}, corpses = []; let zSeq = 1;
const drops = []; let dropSeq = 1;
const L = { vy: 0, onGround: true, bob: 0, weapons: [], wi: 0, fireT: 0, reloadT: 0, switchT: 0, ads: 0, kick: 0, bloom: 0, shake: 0, crouch: 0, stam: 1, stamT: 0, winded: false, brT: 0, vx: 0, vz: 0, land: 0, roll: 0, swx: 0, swy: 0, skin: 0, abRound: -1, fired: false,
  meleeT: 0, meleeHit: false, jy: 0, burstN: 0, nearZ: 99, stingT: -99, ambT: 12, hbT: 0, flick: 0, flash: true, crateT: 0, crateW: null, lastHp: 100, hurt: 0, wasDown: false, hitFx: 0, sprint: false, stepPh: 0 };
const keys = {}, mouse = { l: false, r: false };
const Net = { peer: null, conns: {}, conn: null, sendT: 0 };
let flashlight, muzzleLight, remoteFlash, zGroup, propGroup, doorGroup, shootables = [];
let crateObj = null, msgT = 0, flow = new Int16Array(W * H), flowT = 0;
const gunViews = {}; let gunRoot, muzzleFlash, wLight, knife;
const rnd = (a, b) => a + Math.random() * (b - a);
const lerpAngle = (a, b, t) => { let d = ((b - a + Math.PI) % (Math.PI * 2) + Math.PI * 2) % (Math.PI * 2) - Math.PI; return a + d * Math.min(1, t); };
function seeded(s) { return () => { s = (s * 16807 + 11) % 2147483647; return (s & 0xffff) / 0x10000; }; }

// ---------------------------------------------------------------- audio
let AC = null, master = null, noiseBuf = null, shaper = null;
function initAudio() {
  if (AC) return;
  try {
    AC = new (window.AudioContext || window.webkitAudioContext)();
    master = AC.createGain(); master.gain.value = .5; master.connect(AC.destination);
    noiseBuf = AC.createBuffer(1, AC.sampleRate, AC.sampleRate);
    const d = noiseBuf.getChannelData(0); for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
    // ambience: wind + low drone
    const n = AC.createBufferSource(); n.buffer = noiseBuf; n.loop = true;
    const f = AC.createBiquadFilter(); f.type = 'lowpass'; f.frequency.value = 260;
    const g = AC.createGain(); g.gain.value = .09;
    const lfo = AC.createOscillator(); lfo.frequency.value = .09; const lg = AC.createGain(); lg.gain.value = .05;
    lfo.connect(lg).connect(g.gain); lfo.start();
    n.connect(f).connect(g).connect(master); n.start();
    // uneasy drone: close, beating low tones with a slow swell, plus a thin high whine that drifts
    const dg = AC.createGain(); dg.gain.value = .05; dg.connect(master); const dl = AC.createOscillator(); dl.frequency.value = .05; const dlg = AC.createGain(); dlg.gain.value = .03; dl.connect(dlg).connect(dg.gain); dl.start();
    for (const fr of [41, 43.6, 58.3, 61.7]) { const o = AC.createOscillator(); o.type = fr > 50 ? 'triangle' : 'sine'; o.frequency.value = fr; const og = AC.createGain(); og.gain.value = fr > 50 ? .35 : 1; o.connect(og).connect(dg); o.start(); }
    const hw = AC.createOscillator(); hw.frequency.value = 1870; const hwl = AC.createOscillator(); hwl.frequency.value = .07; const hwlg = AC.createGain(); hwlg.gain.value = 60; hwl.connect(hwlg).connect(hw.frequency); hwl.start();
    const hwg = AC.createGain(); hwg.gain.value = .0035; hw.connect(hwg).connect(master); hw.start();
    shaper = AC.createWaveShaper(); const cv = new Float32Array(256); for (let i = 0; i < 256; i++) { const x = i / 128 - 1; cv[i] = Math.tanh(x * 5); } shaper.curve = cv;
    initMusic(); loadClips();
  } catch (e) { AC = null; }
}
function sNoise(freq, dur, vol, type) {
  if (!AC) return; const t = AC.currentTime;
  const s = AC.createBufferSource(); s.buffer = noiseBuf; s.playbackRate.value = rnd(.8, 1.2);
  const f = AC.createBiquadFilter(); f.type = type || 'lowpass';
  f.frequency.setValueAtTime(freq * 5, t); f.frequency.exponentialRampToValueAtTime(Math.max(40, freq * .35), t + dur);
  const g = AC.createGain(); g.gain.setValueAtTime(vol, t); g.gain.exponentialRampToValueAtTime(.001, t + dur * 1.5);
  s.connect(f).connect(g).connect(master); s.start(t, Math.random() * .5); s.stop(t + dur * 1.6);
}
function sTone(freq, dur, vol, type, when, slideTo) {
  if (!AC) return; const t = AC.currentTime + (when || 0);
  const o = AC.createOscillator(); o.type = type || 'sine'; o.frequency.setValueAtTime(freq, t);
  if (slideTo) o.frequency.exponentialRampToValueAtTime(slideTo, t + dur);
  const g = AC.createGain(); g.gain.setValueAtTime(.0001, t); g.gain.linearRampToValueAtTime(vol, t + .01); g.gain.exponentialRampToValueAtTime(.001, t + dur);
  o.connect(g).connect(master); o.start(t); o.stop(t + dur + .05);
}
const SHOT = { pistol: [900, .13, .8], smg: [1300, .09, .6], shotgun: [480, .3, 1.1], rifle: [1000, .15, .85], dmr: [650, .28, 1.1], lmg: [800, .16, .9] };
let lastTail = 0, lastFlesh = 0;
function sShot(kind, vol) {
  const P = SHOT[kind] || SHOT.pistol; vol = vol === undefined ? 1 : vol; if (vol < .02) return;
  sNoise(P[0], P[1], P[2] * vol); sNoise(300, .6, .18 * vol); sTone(150, .14, .7 * vol, 'sine', 0, 40); sNoise(5200, .025, .45 * vol, 'highpass');
  if (AC.currentTime - lastTail > .16) { lastTail = AC.currentTime; setTimeout(() => { sNoise(P[0] * .45, P[1] * 3, P[2] * vol * .2); sNoise(180, .9, .1 * vol); }, 120); }   // the shot coming back off the walls
}
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
function outNode(pan) { if (pan && AC.createStereoPanner) { const p = AC.createStereoPanner(); p.pan.value = clamp(pan, -1, 1); p.connect(master); return p; } return master; }
// where a sound is, left to right, relative to the way you are facing
function panOf(x, z) { if (!me) return 0; const dx = x - me.x, dz = z - me.z; return clamp((dx * Math.cos(me.yaw) - dz * Math.sin(me.yaw)) / Math.max(2.5, Math.hypot(dx, dz)), -1, 1); }
function voice(f0, f1, dur, vol, pan, o) {   // gritty throat sound: two detuned saws, growl tremolo, moving formant, distortion
  if (!AC || vol < .02) return; const t = AC.currentTime, out = outNode(pan), g = AC.createGain(), f = AC.createBiquadFilter(), ws = AC.createWaveShaper(); ws.curve = shaper.curve;
  f.type = 'bandpass'; f.Q.value = o.q || 2.5; f.frequency.setValueAtTime(o.fa, t); f.frequency.linearRampToValueAtTime(o.fb, t + dur * .5); f.frequency.linearRampToValueAtTime(o.fc || o.fa, t + dur);
  g.gain.setValueAtTime(.0001, t); g.gain.linearRampToValueAtTime(vol, t + (o.att || .08)); g.gain.setValueAtTime(vol, t + dur * .6); g.gain.exponentialRampToValueAtTime(.001, t + dur);
  const am = AC.createGain(); am.gain.value = 1 - (o.am || 0) / 2; const al = AC.createOscillator(); al.type = 'square'; al.frequency.value = o.amf || 38; const alg = AC.createGain(); alg.gain.value = (o.am || 0) / 2; al.connect(alg).connect(am.gain);
  for (const det of [1, 1.013, o.oct ? .5 : 1.5]) { const os = AC.createOscillator(); os.type = 'sawtooth'; os.frequency.setValueAtTime(f0 * det, t); os.frequency.linearRampToValueAtTime(f1 * det, t + dur * .45); os.frequency.linearRampToValueAtTime(f0 * det * (o.end || .8), t + dur);
    const vl = AC.createOscillator(); vl.frequency.value = o.vib || 9; const vg = AC.createGain(); vg.gain.value = f0 * (o.vibd || .03); vl.connect(vg).connect(os.frequency); vl.start(t); vl.stop(t + dur + .1); os.connect(am); os.start(t); os.stop(t + dur + .1); }
  if (o.noise) { const n = AC.createBufferSource(); n.buffer = noiseBuf; const ng = AC.createGain(); ng.gain.value = o.noise; n.connect(ng).connect(am); n.start(t, Math.random()); n.stop(t + dur + .1); }
  am.connect(ws).connect(f).connect(g).connect(out); al.start(t); al.stop(t + dur + .1);
}
// Throat voice: a buzzing glottal source with jitter and vocal fry, pushed through three vowel resonances, with breath mixed in.
const VOW = { a: [730, 1090, 2440], o: [570, 840, 2410], u: [300, 870, 2240], e: [530, 1840, 2480], r: [490, 1350, 1690] };
function vox(o) {
  if (!AC || !(o.vol >= .02)) return; const t = AC.currentTime + (o.when || 0), dur = o.dur, g = AC.createGain(), src = AC.createGain(), f0 = o.f0, f1 = o.f1 || f0, f2 = o.f2 || f1;
  g.gain.setValueAtTime(.0001, t); g.gain.linearRampToValueAtTime(o.vol, t + (o.att || .1)); g.gain.setValueAtTime(o.vol, t + dur * (o.hold || .65)); g.gain.exponentialRampToValueAtTime(.001, t + dur);
  for (const [mul, type, lv] of [[1, 'sawtooth', 1], [1.007, 'sawtooth', .6], [.5, 'square', o.fry === undefined ? .5 : o.fry]]) { if (!lv) continue; const os = AC.createOscillator(); os.type = type;
    os.frequency.setValueAtTime(f0 * mul, t); os.frequency.linearRampToValueAtTime(f1 * mul, t + dur * .4); os.frequency.linearRampToValueAtTime(f2 * mul, t + dur);
    const j = AC.createOscillator(); j.type = 'sawtooth'; j.frequency.value = rnd(17, 31); const jg = AC.createGain(); jg.gain.value = f0 * mul * (o.jit || .04); j.connect(jg).connect(os.frequency); j.start(t); j.stop(t + dur + .1);
    const og = AC.createGain(); og.gain.value = lv; os.connect(og).connect(src); os.start(t); os.stop(t + dur + .1); }
  const n = AC.createBufferSource(); n.buffer = noiseBuf; n.loop = true; const ng = AC.createGain(); ng.gain.value = o.breath === undefined ? .35 : o.breath; n.connect(ng).connect(src); n.start(t, Math.random()); n.stop(t + dur + .1);
  const am = AC.createGain(); am.gain.value = 1 - (o.rat || 0) / 2;
  if (o.rat) { const al = AC.createOscillator(); al.type = 'sawtooth'; al.frequency.setValueAtTime(o.ratf || 28, t); al.frequency.linearRampToValueAtTime((o.ratf || 28) * (o.ratEnd || .6), t + dur); const alg = AC.createGain(); alg.gain.value = o.rat / 2; al.connect(alg).connect(am.gain); al.start(t); al.stop(t + dur + .1); }
  const ws = AC.createWaveShaper(); ws.curve = shaper.curve; const pre = AC.createGain(); pre.gain.value = o.drive || .5; src.connect(am).connect(pre).connect(ws);
  const va = VOW[o.v0 || 'u'], vb = VOW[o.v1 || o.v0 || 'a'], sh = o.shift || 1;
  for (let i = 0; i < 3; i++) { const f = AC.createBiquadFilter(); f.type = 'bandpass'; f.Q.value = [5, 8, 9][i]; f.frequency.setValueAtTime(va[i] * sh, t); f.frequency.linearRampToValueAtTime(vb[i] * sh, t + dur * .5); f.frequency.linearRampToValueAtTime(va[i] * sh * .9, t + dur);
    const fg = AC.createGain(); fg.gain.value = [1.6, 1, .5][i]; ws.connect(f); f.connect(fg).connect(g); }
  const lp = AC.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 220 * sh; const lg = AC.createGain(); lg.gain.value = .6; ws.connect(lp); lp.connect(lg).connect(g);   // chest
  g.connect(outNode(o.pan));
}
const vpick = s => s[(Math.random() * s.length) | 0];
// Recorded zombie voices (snd/README.txt has the source and licence). Sorted by ear-free measurements: long slow ones are moans,
// short sharp ones are attack snarls, bright raspy ones are shrieks. Until they load, or if they fail to, the synth voices below are used.
const ZS = { groan: [16, 17, 18, 21, 15, 20, 2, 1, 23, 22], snarl: [4, 5, 6, 24, 3, 7], scream: [9, 11, 12, 13, 10, 19, 8, 14] }, zbuf = {};
function loadClips() { if (!AC || !window.fetch) return; for (let i = 1; i <= 24; i++) fetch('snd/z' + i + '.mp3').then(r => r.ok ? r.arrayBuffer() : null).then(b => { if (b) AC.decodeAudioData(b, buf => { zbuf[i] = buf; }, () => {}); }).catch(() => {}); }
function clip(kind, vol, pan, rate) {
  if (!AC) return false; const ids = ZS[kind].filter(i => zbuf[i]); if (!ids.length) return false; if (vol < .02) return true;
  const src = AC.createBufferSource(), g = AC.createGain(); src.buffer = zbuf[ids[(Math.random() * ids.length) | 0]]; src.playbackRate.value = rate * rnd(.93, 1.07); g.gain.value = Math.min(1.4, vol);
  src.connect(g); g.connect(outNode(pan)); if (echoIn) { const e = AC.createGain(); e.gain.value = .22; g.connect(e); e.connect(echoIn); } src.start(); return true;
}
function sGroan(vol, pan) { if (clip('groan', vol * 1.1, pan, rnd(.68, 1))) return; const f = rnd(60, 96); vox({ f0: f, f1: f * rnd(1.05, 1.3), f2: f * rnd(.6, .8), dur: rnd(1.3, 2.6), vol: .8 * vol, pan, v0: vpick('uor'), v1: vpick('ao'), rat: rnd(.5, .9), ratf: rnd(20, 34), jit: .05, breath: .3, shift: rnd(.78, 1), att: .25 }); }
function sSnarl(vol, pan) { if (clip('snarl', vol * 1.2, pan, rnd(.88, 1.1))) return; const f = rnd(105, 150); vox({ f0: f, f1: f * 1.6, f2: f * .7, dur: rnd(.4, .65), vol: vol, pan, v0: 'e', v1: 'a', rat: 1, ratf: rnd(40, 55), jit: .08, breath: .7, drive: 1, att: .02, shift: rnd(.85, 1) }); sNoise(2400, .12, vol * .25, 'bandpass'); }
function sScream(vol, pan) { if (clip('scream', vol * 1.1, pan, rnd(.95, 1.2))) return; const f = rnd(250, 360); vox({ f0: f, f1: f * rnd(1.4, 1.8), f2: f * .7, dur: rnd(.8, 1.4), vol: .75 * vol, pan, v0: 'a', v1: 'e', rat: .8, ratf: rnd(50, 70), ratEnd: 1.2, jit: .12, breath: .55, drive: 1, att: .04, fry: .3, shift: rnd(.95, 1.15) }); }
function sHiss(vol, pan) { vox({ f0: 70, dur: rnd(.9, 1.6), vol: .5 * vol, pan, v0: 'e', v1: 'r', rat: .9, ratf: rnd(30, 60), breath: 2.2, fry: .15, att: .2, shift: 1.2 }); }
function sGurgle(vol, pan) { const f = rnd(80, 110); if (!clip('groan', vol, pan, rnd(.52, .68))) vox({ f0: f, f1: f * .8, f2: f * .45, dur: rnd(.9, 1.5), vol: .8 * vol, pan, v0: 'o', v1: 'u', rat: 1, ratf: 20, ratEnd: .25, jit: .07, breath: .6, att: .03, shift: .85 });
  if (vol > .1) for (let i = 0; i < 5; i++) sTone(rnd(180, 420), .05, vol * .1, 'sine', .2 + i * rnd(.07, .14), 90); }
// something forcing its way up through the floor
function sSpawn(vol, pan) { if (vol < .04) return; sNoise(85, 1.2, vol * .9); sTone(44, .5, vol * .7, 'sine', 0, 26); for (let i = 0; i < 4; i++) setTimeout(() => sNoise(rnd(1500, 2600), rnd(.08, .2), vol * .3, 'bandpass'), 150 + i * rnd(140, 260));
  if (clip('groan', vol, pan, rnd(.45, .55))) return; const f = rnd(48, 62); vox({ f0: f, f1: f * 1.9, f2: f * 1.3, dur: 1.3, vol: .8 * vol, pan, v0: 'u', v1: 'a', rat: 1, ratf: 16, ratEnd: 2.4, breath: .6, att: .5, shift: .8, when: .25 }); }
function sFlesh(head) { if (!AC || AC.currentTime - lastFlesh < .06) return; lastFlesh = AC.currentTime; sNoise(650, .08, .55, 'bandpass'); sNoise(1900, .05, .22, 'bandpass'); sTone(105, .08, .55, 'sine', 0, 45); if (head) sCrack(.6); }
function sHurt() { sTone(72, .2, .85, 'sine', 0, 34); sNoise(950, .18, .5, 'bandpass'); sNoise(300, .12, .5); sTone(3300, 1.1, .025, 'sine');
  vox({ f0: rnd(140, 170), f1: 120, f2: 95, dur: .38, vol: .45, pan: 0, v0: 'a', v1: 'o', breath: .6, fry: .1, att: .02, jit: .03 }); }
// a far-off siren winding up and down, and the mains dying
function sSiren(vol, dur) { if (!AC) return; const t = AC.currentTime, g = AC.createGain(), lp = AC.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 1000;
  g.gain.setValueAtTime(.0001, t); g.gain.linearRampToValueAtTime(vol, t + 1.4); g.gain.setValueAtTime(vol, t + dur - 2); g.gain.linearRampToValueAtTime(.0001, t + dur);
  for (const [d, ty] of [[1, 'sawtooth'], [1.013, 'sawtooth'], [.5, 'triangle'], [1.41, 'sine']]) { const o = AC.createOscillator(); o.type = ty; const f = 233 * d;
    o.frequency.setValueAtTime(f * .6, t); o.frequency.exponentialRampToValueAtTime(f * 1.9, t + dur * .38); o.frequency.exponentialRampToValueAtTime(f * 1.75, t + dur * .6); o.frequency.exponentialRampToValueAtTime(f * .5, t + dur); o.connect(lp); o.start(t); o.stop(t + dur + .1); }
  lp.connect(g); g.connect(master); if (echoIn) g.connect(echoIn); }
function sPowerDown() { sNoise(100, .16, .8); sTone(880, 1.6, .1, 'triangle', .05, 50); sTone(120, 1.8, .3, 'sine', .05, 24); sSiren(.045, 5); }
function sSting() {   // jump scare: a dissonant stab with a sub drop under it
  if (!AC) return; for (const f of [207, 220, 311, 440, 466, 932]) sTone(f, 1.3, .1, 'sawtooth', 0, f * .97); sNoise(1800, .25, .5, 'highpass'); sTone(120, .9, .7, 'sine', 0, 28);
}
function sHeart(v) { sTone(58, .13, .5 * v, 'sine', 0, 34); sTone(52, .15, .38 * v, 'sine', .21, 30); }
function sWhisper(vol) {
  if (!AC) return; const t = AC.currentTime, d = rnd(1.4, 2.8), n = AC.createBufferSource(); n.buffer = noiseBuf; n.loop = true; const f = AC.createBiquadFilter(); f.type = 'bandpass'; f.Q.value = 7;
  f.frequency.setValueAtTime(rnd(1200, 2400), t); for (let i = 1; i < 9; i++) f.frequency.linearRampToValueAtTime(rnd(900, 3200), t + d * i / 9);
  const g = AC.createGain(); g.gain.setValueAtTime(.0001, t); for (let i = 1; i < 12; i++) g.gain.linearRampToValueAtTime(i % 2 ? .1 * vol : .015 * vol, t + d * i / 12); g.gain.linearRampToValueAtTime(.0001, t + d);
  n.connect(f).connect(g).connect(outNode(rnd(-1, 1))); n.start(t, Math.random()); n.stop(t + d + .1);
}
function sThunder() { sNoise(70, 2.6, .9); sNoise(160, 1.2, .5); sTone(48, 2.2, .5, 'sine', 0, 26); }
function sClang(vol, pan) { if (!AC) return; const t = AC.currentTime, out = outNode(pan); for (const f of [173, 311, 487, 742, 1130]) { const o = AC.createOscillator(); o.frequency.value = f * rnd(.98, 1.02); const g = AC.createGain(); g.gain.setValueAtTime(vol * .12, t); g.gain.exponentialRampToValueAtTime(.0005, t + rnd(1.2, 2.6)); o.connect(g).connect(out); o.start(t); o.stop(t + 2.8); } }
// ---- music: a slow minor pad and a broken music box while it is quiet; pulsing low strings and a tremolo cluster as they close in
let musicG = null, mLow = null, highG = null, echoIn = null, musicOn = true, mNext = 3, mStep = 0, tension = 0;
function initMusic() {
  musicG = AC.createGain(); musicG.gain.value = .9; musicG.connect(master);
  echoIn = AC.createGain(); const dl = AC.createDelay(1); dl.delayTime.value = .43; const fb = AC.createGain(); fb.gain.value = .52; const ef = AC.createBiquadFilter(); ef.type = 'lowpass'; ef.frequency.value = 1700;
  echoIn.connect(dl); dl.connect(ef); ef.connect(fb); fb.connect(dl); ef.connect(musicG);
  mLow = AC.createBiquadFilter(); mLow.type = 'lowpass'; mLow.frequency.value = 420; mLow.Q.value = 3; mLow.connect(musicG);
  const pf = AC.createBiquadFilter(); pf.type = 'lowpass'; pf.frequency.value = 300; const pg = AC.createGain(); pg.gain.value = .045; pf.connect(pg).connect(musicG);
  const pl = AC.createOscillator(); pl.frequency.value = .04; const plg = AC.createGain(); plg.gain.value = 140; pl.connect(plg).connect(pf.frequency); pl.start();
  for (const fr of [73.42, 73.9, 110, 110.7, 174.6, 207.65]) { const o = AC.createOscillator(); o.type = 'sawtooth'; o.frequency.value = fr; const og = AC.createGain(); og.gain.value = fr > 200 ? .3 : 1; o.connect(og).connect(pf); o.start(); }
  highG = AC.createGain(); highG.gain.value = 0; highG.connect(musicG); const hf = AC.createBiquadFilter(); hf.type = 'bandpass'; hf.frequency.value = 1500; hf.Q.value = .8;
  const tr = AC.createGain(); tr.gain.value = .6; const tl = AC.createOscillator(); tl.frequency.value = 10.5; const tlg = AC.createGain(); tlg.gain.value = .4; tl.connect(tlg).connect(tr.gain); tl.start();
  for (const fr of [622.3, 659.3, 932.3, 987.8]) { const o = AC.createOscillator(); o.type = 'sawtooth'; o.frequency.value = fr; o.connect(hf); o.start(); }
  hf.connect(tr).connect(highG);
}
function mNote(f, dur, vol, type, dest, echo, when) {
  if (!AC || !musicG) return; const t = AC.currentTime + (when || 0), o = AC.createOscillator(), g = AC.createGain(); o.type = type; o.frequency.value = f;
  g.gain.setValueAtTime(.0001, t); g.gain.linearRampToValueAtTime(vol, t + .012); g.gain.exponentialRampToValueAtTime(.0005, t + dur);
  o.connect(g); g.connect(dest || musicG); if (echo) g.connect(echoIn); o.start(t); o.stop(t + dur + .05);
}
const BOX = [293.66, 349.23, 440, 466.16, 554.37, 587.33, 698.46], OST = [73.42, 73.42, 87.31, 73.42, 103.83, 73.42, 87.31, 69.3];
function musicUpdate(dt) {
  if (!AC || !musicG || !me) return;
  const near = me.down ? .2 : clamp((13 - L.nearZ) / 11, 0, 1), wave = G.state === 'wave';
  const tgt = clamp(Math.max(near, me.down ? 0 : 1 - me.hp / me.maxHp) * (wave ? 1 : .5) + (wave ? .1 : 0) + (G.evacT > 0 ? .35 : 0) + (blackT > 0 ? .3 : 0), 0, 1);
  tension += (tgt - tension) * Math.min(1, dt * (tgt > tension ? 1.6 : .3));
  highG.gain.setTargetAtTime(tension * tension * .06, AC.currentTime, .25); mLow.frequency.setTargetAtTime(300 + tension * 700, AC.currentTime, .3);
  mNext -= dt; if (mNext > 0) return;
  if (tension > .33) { const f = OST[mStep++ % 8]; mNote(f, .24, .1 + tension * .16, 'sawtooth', mLow); mNote(f * 2, .2, .03 + tension * .05, 'square', mLow);
    if (mStep % 4 === 1) mNote(52, .3, .25 + tension * .2, 'sine'); if (tension > .75 && mStep % 8 === 5) mNote(1108.7, .5, .03, 'sawtooth', null, true);
    mNext = .44 - tension * .2; }
  else { const f = BOX[(Math.random() * BOX.length) | 0] * (Math.random() < .3 ? .5 : 1); mNote(f, 2.8, .05, 'triangle', null, true); mNote(f * 2.01, 1.2, .012, 'sine', null, true);
    if (Math.random() < .3) mNote(f * 1.0595, 2.4, .028, 'triangle', null, true, .5);   // a wrong note, half a beat late
    mNext = rnd(1.4, 4.2); }
}
function sCrack(vol) { if (vol < .03) return; sNoise(2600, .05, vol * .8, 'highpass'); sTone(190, .09, vol * .7, 'square', 0, 55); sNoise(420, .2, vol * .6, 'bandpass'); }
function sStomp(vol) { if (vol < .03) return; sTone(46, .3, vol, 'sine', 0, 24); sNoise(90, .18, vol * .6); }
function sBreath(vol) { sNoise(1100, .32, vol, 'bandpass'); setTimeout(() => sNoise(700, .4, vol * .7, 'bandpass'), 420); }
function sRiser(dur) { if (!AC) return; const t = AC.currentTime; for (const f of [180, 191, 270]) { const o = AC.createOscillator(), g = AC.createGain(); o.type = 'sawtooth'; o.frequency.setValueAtTime(f, t); o.frequency.exponentialRampToValueAtTime(f * 4, t + dur);
  g.gain.setValueAtTime(.0001, t); g.gain.exponentialRampToValueAtTime(.09, t + dur); g.gain.linearRampToValueAtTime(.0001, t + dur + .03); o.connect(g).connect(master); o.start(t); o.stop(t + dur + .1); } }
function ambientEvent() {   // things you hear but never find
  const k = Math.random(), pan = rnd(-1, 1);
  if (k < .22) sScream(rnd(.1, .22), pan); else if (k < .42) sWhisper(rnd(.5, 1)); else if (k < .58) sClang(rnd(.3, .7), pan);
  else if (k < .74) { for (let i = 0; i < 3; i++) setTimeout(() => sNoise(110, .1, .35), i * rnd(260, 420)); } else if (k < .88) sGroan(rnd(.2, .4), pan);
  else { for (let i = 0; i < 5; i++) setTimeout(() => sNoise(150, .06, .12 + i * .04), i * 330); }   // footsteps coming closer
}
const distVol = (x, z, range) => me ? Math.max(0, 1 - Math.hypot(x - me.x, z - me.z) / range) : 0;

// ---------------------------------------------------------------- textures
function canvasTex(size, fn, srgb) {
  const c = document.createElement('canvas'); c.width = c.height = size; const g = c.getContext('2d'); fn(g, size);
  const t = new THREE.CanvasTexture(c); t.wrapS = t.wrapT = THREE.RepeatWrapping; t.anisotropy = 8;
  if (srgb !== false) t.encoding = THREE.sRGBEncoding; return t;
}
function grainFx(g, s, amt) {
  const d = g.getImageData(0, 0, s, s), a = d.data;
  for (let i = 0; i < a.length; i += 4) { const n = (Math.random() - .5) * amt; a[i] += n; a[i + 1] += n; a[i + 2] += n; }
  g.putImageData(d, 0, 0);
}
function blotch(g, s, n, col, r0, r1, al) {
  for (let i = 0; i < n; i++) {
    const x = Math.random() * s, y = Math.random() * s, r = rnd(r0, r1), gr = g.createRadialGradient(x, y, 0, x, y, r);
    gr.addColorStop(0, `rgba(${col},${al})`); gr.addColorStop(1, `rgba(${col},0)`);
    g.fillStyle = gr; g.fillRect(x - r, y - r, r * 2, r * 2);
  }
}
function cracks(g, s, n, col) {
  g.strokeStyle = col; g.lineWidth = 1;
  for (let i = 0; i < n; i++) { let x = Math.random() * s, y = Math.random() * s; g.beginPath(); g.moveTo(x, y);
    for (let k = 0; k < 14; k++) { x += rnd(-12, 12); y += rnd(2, 16); g.lineTo(x, y); } g.stroke(); }
}
function wallTex(v) {
  return canvasTex(512, (g, s) => {
    g.fillStyle = v ? '#6d7166' : '#727868'; g.fillRect(0, 0, s, s);
    g.fillStyle = v ? '#3b4640' : '#434b41'; g.fillRect(0, s * .6, s, s * .4);
    g.fillStyle = '#23261f'; g.fillRect(0, s * .6 - 3, s, 6);
    blotch(g, s, 40, '25,28,20', 20, 90, .35); blotch(g, s, 14, '120,120,100', 10, 50, .25);
    for (let i = 0; i < 26; i++) { const x = Math.random() * s, y = Math.random() * s * .5, h = rnd(60, 260), gr = g.createLinearGradient(0, y, 0, y + h);
      gr.addColorStop(0, 'rgba(30,26,16,.5)'); gr.addColorStop(1, 'rgba(30,26,16,0)'); g.fillStyle = gr; g.fillRect(x, y, rnd(2, 7), h); }
    cracks(g, s, 9, 'rgba(15,15,12,.7)');
    if (v) { blotch(g, s, 5, '90,8,6', 15, 55, .7); g.fillStyle = 'rgba(80,6,5,.6)'; for (let i = 0; i < 5; i++) g.fillRect(200 + i * 11, 250 + rnd(-8, 8), 6, rnd(30, 120)); }
    const gr = g.createLinearGradient(0, s * .78, 0, s); gr.addColorStop(0, 'rgba(0,0,0,0)'); gr.addColorStop(1, 'rgba(0,0,0,.75)'); g.fillStyle = gr; g.fillRect(0, s * .78, s, s * .22);
    grainFx(g, s, 34);
  });
}
function bumpTex() {
  return canvasTex(256, (g, s) => { g.fillStyle = '#808080'; g.fillRect(0, 0, s, s); blotch(g, s, 60, '40,40,40', 6, 30, .5); blotch(g, s, 40, '200,200,200', 4, 20, .4); cracks(g, s, 8, '#111'); grainFx(g, s, 90); }, false);
}

// ---------------------------------------------------------------- level kit
const MAT = {}, KGEO = {};
let levelGroup = null, glowMesh = null, skyGroup = null, hemi = null, sun = null, lightT = 0, blackT = 0, blackNext = 50, flashT = 0, flashNext = 20;
const lightSpots = [], pool = [], weatherPts = [];
let LR = Math.random;                         // seeded while a map is generated, so every player builds the identical level
const lr = (a, b) => a + LR() * (b - a), lpick = n => (LR() * n) | 0;
let instQ = {}, wallQ = {}, glowQ = [], PY = 0, PL = 0, heli = null, crateShow = null, OBJ = { gens: [], sups: [], zone: null, list: [] };
const V3 = (x, y, z) => new THREE.Vector3(x, y, z);
function M(x, y, z, rx, ry, rz, sx, sy, sz) {
  return new THREE.Matrix4().compose(V3(x, y, z), new THREE.Quaternion().setFromEuler(new THREE.Euler(rx || 0, ry || 0, rz || 0)), V3(sx || 1, sy || 1, sz || 1));
}
// merge coloured primitives into one mesh: lots of surface detail for a single draw call
function mergedC(parts) {
  const pos = [], nor = [], uv = [], col = [], c = new THREE.Color();
  for (const [g0, m, hex] of parts) {
    const g = g0.index ? g0.toNonIndexed() : g0.clone(); if (m) g.applyMatrix4(m);
    const p = g.attributes.position.array, n = g.attributes.normal.array, u = g.attributes.uv ? g.attributes.uv.array : null;
    c.set(hex === undefined ? 0xffffff : hex).convertSRGBToLinear();
    for (let i = 0; i < p.length; i += 3) { pos.push(p[i], p[i + 1], p[i + 2]); nor.push(n[i], n[i + 1], n[i + 2]); col.push(c.r, c.g, c.b); }
    for (let i = 0; i < p.length / 3; i++) uv.push(u ? u[i * 2] : 0, u ? u[i * 2 + 1] : 0);
  }
  const o = new THREE.BufferGeometry();
  o.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); o.setAttribute('normal', new THREE.Float32BufferAttribute(nor, 3));
  o.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); o.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
  return o;
}
function flat(g0) { const g = g0.index ? g0.toNonIndexed() : g0; g.computeVertexNormals(); return g; }
function q4(rt, rb, h) { const g = new THREE.CylinderGeometry(rt, rb, h, 4); g.rotateY(Math.PI / 4); return flat(g); }   // tapered box
function Kit() {
  const parts = [], K = {
    b: (w, h, l, x, y, z, col, rx, ry, rz) => { parts.push([new THREE.BoxGeometry(w, h, l), M(x, y, z, rx, ry, rz), col]); return K; },
    c: (rt, rb, h, x, y, z, col, n, rx, ry, rz) => { parts.push([new THREE.CylinderGeometry(rt, rb, h, n || 10), M(x, y, z, rx, ry, rz), col]); return K; },
    s: (r, x, y, z, col, sx, sy, sz) => { parts.push([new THREE.SphereGeometry(r, 10, 8), M(x, y, z, 0, 0, 0, sx, sy, sz), col]); return K; },
    g: (geo, m, col) => { parts.push([geo, m, col]); return K; },
    seg: (rA, rB, A, B, col, n) => { const a = V3(A[0], A[1], A[2]), b = V3(B[0], B[1], B[2]), d = b.clone().sub(a), len = d.length();
      const q = new THREE.Quaternion().setFromUnitVectors(V3(0, 1, 0), d.normalize());
      parts.push([new THREE.CylinderGeometry(rB, rA, len, n || 6), new THREE.Matrix4().compose(a.add(b).multiplyScalar(.5), q, V3(1, 1, 1)), col]); return K; },
    done: () => mergedC(parts)
  };
  return K;
}
function lump(detail, amp) {      // irregular rock-like blob, flat shaded
  const g = new THREE.IcosahedronGeometry(1, detail), p = g.attributes.position;
  for (let i = 0; i < p.count; i++) { const x = p.getX(i), y = p.getY(i), z = p.getZ(i);
    const n = 1 + amp * Math.sin(x * 7.3 + y * 3.1) * Math.cos(z * 5.7 + x * 2.2) + amp * .45 * Math.sin(y * 11 + z * 4);
    p.setXYZ(i, x * n, Math.max(-.35, y * n * .78) + .35, z * n); }
  return flat(g);
}
const KITS = {
  cube: K => K.b(1, 1, 1, 0, 0, 0),
  car: K => { const bd = 0xffffff, dk = 0x0b0b0d, gl = 0x121a20;
    K.b(1.78, .52, 4.3, 0, .64, 0, bd).b(1.72, .16, 4.2, 0, .33, 0, dk).b(1.6, .04, 1.5, 0, .915, 1.38, bd).b(1.6, .04, 1.0, 0, .915, -1.62, bd)
     .g(q4(.8, 1.17, .56), M(0, 1.17, .2, 0, 0, 0, 1, 1, 1.6), gl).g(q4(.806, 1.176, .56), M(0, 1.17, .2, 0, 0, 0, 1, 1, .07), bd).b(1.15, .05, 1.84, 0, 1.46, .2, bd)
     .b(1.82, .2, .14, 0, .5, 2.2, dk).b(1.82, .2, .14, 0, .5, -2.2, dk).b(.9, .16, .05, 0, .62, 2.16, dk).b(.42, .12, .03, 0, .56, -2.23, 0xb0b0a8)
     .b(1.8, .46, .014, 0, .66, .78, dk).b(1.8, .46, .014, 0, .66, -.36, dk).b(1.82, .03, .14, 0, .82, .55, dk).b(1.82, .03, .14, 0, .82, -.58, dk).b(1.5, .012, .014, 0, .94, 1.0, dk);
    for (const s of [-1, 1]) { K.b(.36, .13, .05, s * .62, .74, 2.16, 0xcfcfb8).b(.36, .12, .05, s * .62, .76, -2.16, 0x5a0c0c).b(.14, .09, .1, s * .96, 1.0, 1.02, bd);
      for (const e of [-1.38, 1.38]) K.c(.33, .33, .22, s * .84, .33, e, 0x0a0a0a, 14, 0, 0, Math.PI / 2).c(.17, .17, .24, s * .84, .33, e, 0x6c6e70, 10, 0, 0, Math.PI / 2).b(.06, .3, .8, s * .9, .62, e, dk); } },
  van: K => { const bd = 0xffffff, dk = 0x0b0b0d, gl = 0x121a20;
    K.b(1.95, 1.5, 4.9, 0, 1.22, 0, bd).b(1.9, .2, 4.8, 0, .38, 0, dk).b(1.7, .62, .05, 0, 1.56, 2.45, gl).b(1.97, .5, 1.05, 0, 1.6, 1.72, gl).b(1.97, 1.2, .016, 0, 1.2, 1.1, dk).b(1.97, 1.2, .016, 0, 1.2, -.4, dk)
     .b(.02, 1.3, .02, 0, 1.2, -2.46, dk).b(1.5, .5, .03, 0, 1.62, -2.46, gl).b(2.0, .22, .16, 0, .5, 2.48, dk).b(2.0, .22, .16, 0, .5, -2.48, dk).b(1.6, .08, 2.6, 0, 2.0, -.6, 0x2a2c2e);
    for (const s of [-1, 1]) { K.b(.34, .16, .05, s * .7, .9, 2.46, 0xcfcfb8).b(.2, .4, .05, s * .82, 1.1, -2.46, 0x5a0c0c).b(.14, .2, .1, s * 1.05, 1.5, 2.0, dk);
      for (const e of [-1.55, 1.6]) K.c(.36, .36, .24, s * .9, .36, e, 0x0a0a0a, 14, 0, 0, Math.PI / 2).c(.18, .18, .26, s * .9, .36, e, 0x6c6e70, 10, 0, 0, Math.PI / 2); } },
  lamp: K => K.c(.16, .22, .5, 0, .25, 0, 0x24272a, 8).c(.06, .09, 5.9, 0, 3.2, 0, 0x2c3033, 8).c(.1, .1, .12, 0, 2.0, 0, 0x1c1e20, 8).b(.09, .09, 1.7, 0, 6.1, .75, 0x2c3033).b(.34, .14, .78, 0, 6.05, 1.5, 0x34383b).seg(.02, .02, [0, 5.3, 0], [0, 6.05, .9], 0x2c3033),
  lantern: K => { K.c(.05, .07, 2.3, 0, 1.15, 0, 0x2a2118, 6).b(.05, .05, .55, 0, 2.22, .24, 0x2a2118).b(.02, .14, .02, 0, 2.12, .45, 0x121212).b(.2, .04, .2, 0, 2.04, .45, 0x151515).b(.17, .04, .17, 0, 1.72, .45, 0x151515).c(.02, .06, .08, 0, 2.1, .45, 0x151515, 6);
    for (const a of [[-1, -1], [1, -1], [-1, 1], [1, 1]]) K.b(.015, .3, .015, a[0] * .075, 1.88, .45 + a[1] * .075, 0x151515); },
  barrier: K => K.b(.62, .28, 2.96, 0, .14, 0, 0x6f7173).b(.44, .34, 2.96, 0, .45, 0, 0x7c7e80).b(.26, .42, 2.96, 0, .83, 0, 0x858789).b(.63, .12, .6, 0, .2, .8, 0x8a5a20).b(.63, .12, .6, 0, .2, -.8, 0x8a5a20).b(.3, .06, .2, 0, 1.06, 0, 0x55575a),
  pineL: K => { K.c(.1, .2, 2.6, 0, 1.3, 0, 0x241a12, 6); for (let i = 0; i < 5; i++) { const r = 1.75 - i * .32, y = 1.9 + i * 1.05; K.g(new THREE.ConeGeometry(r, 1.7, 7), M(0, y + .85, 0, 0, i * .7, 0), i % 2 ? 0x15231a : 0x1a2b1f).g(new THREE.ConeGeometry(r * .78, .9, 7), M(0, y + 1.32, 0, 0, i * .7 + .3, 0), 0x8e9aac); } },   // light version for the wall of forest round the edge
  pine: K => { K.c(.07, .2, 3.2, 0, 1.6, 0, 0x241a12, 7).c(.2, .3, .35, 0, .17, 0, 0x1e150e, 7);
    for (let i = 0; i < 5; i++) { const a = i * 1.26; K.seg(.07, .02, [Math.cos(a) * .16, .2, Math.sin(a) * .16], [Math.cos(a) * .5, -.05, Math.sin(a) * .5], 0x1e150e, 5); }   // roots
    for (let i = 0; i < 3; i++) { const a = i * 2.3 + .5, y = .9 + i * .4; K.seg(.025, .008, [0, y, 0], [Math.cos(a) * .55, y - .12, Math.sin(a) * .55], 0x1a130d, 4); }   // dead lower stubs
    for (let t = 0; t < 6; t++) { const y = 1.75 + t * .95, len = 1.85 - t * .27, n = t < 4 ? 6 : 5;
      K.g(new THREE.ConeGeometry(len * .5, 1.2, 7), M(0, y + .5, 0, 0, t * .7, 0), 0x101c14);   // dense core
      for (let j = 0; j < n; j++) { const a = j / n * 6.283 + t * .9, cx = Math.cos(a), cz = Math.sin(a), dr = .32 + t * .02;
        K.seg(.38 - t * .03, .02, [cx * .08, y + .3, cz * .08], [cx * len, y + .3 - len * dr, cz * len], j % 2 ? 0x15231a : 0x1a2b1f, 4);   // drooping bough
        if (j % 2 === t % 2) K.seg(.3 - t * .025, .02, [cx * .12, y + .36, cz * .12], [cx * len * .72, y + .355 - len * dr * .72, cz * len * .72], 0x8e9aac, 4); } }   // snow lying on it
    K.g(new THREE.ConeGeometry(.24, 1, 6), M(0, 7.75, 0), 0x15231a).g(new THREE.ConeGeometry(.17, .55, 6), M(0, 8.05, 0), 0xaab6c6); },
  dtree: K => { K.c(.1, .26, 4.6, 0, 2.3, 0, 0x1c1712, 8).c(.3, .38, .34, 0, .17, 0, 0x1c1712, 8);
    for (let i = 0; i < 6; i++) { const a = i * 1.05 + .3; K.seg(.09, .025, [Math.cos(a) * .2, .25, Math.sin(a) * .2], [Math.cos(a) * .75, -.06, Math.sin(a) * .75], 0x19140f, 5); }   // roots
    for (let i = 0; i < 4; i++) K.s(.07, Math.cos(i * 1.9) * .15, 1 + i * .8, Math.sin(i * 1.9) * .15, 0x17120d, 1, 1.3, 1);   // knots
    K.s(.06, 0, 1.9, .17, 0x050403, 1, 1.5, .5);   // hollow
    for (let i = 0; i < 10; i++) { const a = i * 2.4, h = 2 + i * .28, l = 2 - i * .13, bx = Math.cos(a) * l, bz = Math.sin(a) * l, e = [bx, h + l * .55, bz];
      K.seg(.075, .03, [0, h, 0], e, 0x1c1712, 6);
      for (let j = 0; j < 3; j++) { const f = .45 + j * .25, p = [bx * f, h + l * .55 * f, bz * f], a2 = a + (j % 2 ? 1 : -1) * (.7 + j * .2), l2 = l * (.55 - j * .1), q = [p[0] + Math.cos(a2) * l2, p[1] + l2 * (.5 + j * .15), p[2] + Math.sin(a2) * l2];
        K.seg(.028, .01, p, q, 0x1c1712, 4).seg(.01, .003, q, [q[0] + Math.cos(a2 + .8) * l2 * .5, q[1] + l2 * .35, q[2] + Math.sin(a2 + .8) * l2 * .5], 0x1c1712, 3).seg(.01, .003, q, [q[0] + Math.cos(a2 - .9) * l2 * .45, q[1] + l2 * .2, q[2] + Math.sin(a2 - .9) * l2 * .45], 0x1c1712, 3); }
      K.seg(.03, .008, e, [bx * 1.35, h + l * 1.15, bz * 1.35], 0x1c1712, 4); } },
  rock: K => K.g(lump(1, .26), null, 0xffffff),
  deb: K => K.g(flat(new THREE.DodecahedronGeometry(1, 0)), M(0, .35, 0, .4, .3, .2, 1, .7, 1), 0xffffff),
  rubble: K => { for (let i = 0; i < 9; i++) { const a = i * 2.1, d = .25 + (i % 4) * .28, s = .16 + ((i * 7) % 5) * .07;
      K.g(flat(new THREE.DodecahedronGeometry(1, 0)), M(Math.cos(a) * d, s * .6, Math.sin(a) * d, i, i * 2, i * 3, s * 1.3, s, s * 1.1), i % 3 ? 0x6a6c6e : 0x7a6258); }
    K.seg(.012, .012, [-.3, .1, .2], [.5, .7, -.1], 0x3a2418, 5).seg(.012, .012, [.2, .1, -.4], [-.2, .55, .3], 0x3a2418, 5).b(.9, .06, .5, .1, .12, .1, 0x5a5c5e, .2, .5, .1); },
  log: K => K.c(.2, .23, 2.4, 0, .2, 0, 0x2a1f15, 9, 0, 0, Math.PI / 2).c(.19, .19, 2.42, 0, .2, 0, 0x8a7458, 9, 0, 0, Math.PI / 2).c(.2, .2, 1.2, .2, .3, 0, 0xaab6c6, 9, 0, 0, Math.PI / 2).seg(.05, .03, [.5, .3, 0], [.7, .7, .2], 0x2a1f15),
  stump: K => K.c(.24, .3, .5, 0, .25, 0, 0x2a1f15, 9).c(.23, .23, .02, 0, .505, 0, 0x8a7458, 9).c(.2, .2, .08, 0, .53, 0, 0xaab6c6, 9),
  drift: K => K.g(new THREE.SphereGeometry(1, 18, 12), null, 0xb2bdcb),
  logs: K => { for (let i = 0; i < 5; i++) K.seg(.07, .06, [Math.cos(i * 1.26) * .5, .06, Math.sin(i * 1.26) * .5], [-Math.cos(i * 1.26) * .12, .5, -Math.sin(i * 1.26) * .12], 0x1a120c, 7);
    for (let i = 0; i < 8; i++) K.g(flat(new THREE.DodecahedronGeometry(.14, 0)), M(Math.cos(i * .785) * .7, .08, Math.sin(i * .785) * .7, i, i, i), 0x4a4c4e); },
  bed: K => { K.b(2.0, .06, .86, 0, .55, 0, 0x8a8f92).b(1.9, .16, .8, 0, .66, 0, 0xa9a591).b(.5, .1, .6, -.66, .78, 0, 0xb9b6a8).b(1.0, .03, .82, .3, .75, 0, 0x6a7468).b(.05, .5, .86, -1.0, .8, 0, 0x8a8f92).b(.05, .3, .86, 1.0, .7, 0, 0x8a8f92).b(.5, .012, .4, .2, .766, .1, 0x4a0c0a);
    for (const a of [[-.92, -.38], [.92, -.38], [-.92, .38], [.92, .38]]) K.c(.025, .025, .52, a[0], .26, a[1], 0x6a6f72, 6).c(.05, .05, .04, a[0], .03, a[1], 0x151515, 8);
    K.b(1.5, .03, .03, 0, .95, .42, 0x8a8f92).b(.03, .3, .03, -.7, .82, .42, 0x8a8f92).b(.03, .3, .03, .7, .82, .42, 0x8a8f92).seg(.012, .012, [-.9, .5, -.4], [-.9, 1.9, -.4], 0x8a8f92, 5).b(.14, .2, .05, -.9, 1.75, -.34, 0x9aa8a0); },
  locker: K => { for (const x of [-.47, .47]) { K.b(.9, 1.95, .5, x, .98, 0, 0x4a5a55).b(.84, 1.84, .02, x, .98, .255, 0x55665f).b(.03, .12, .03, x + .3, 1.05, .275, 0x1a1a1a);
      for (let i = 0; i < 4; i++) K.b(.4, .015, .01, x, 1.72 - i * .05, .268, 0x1c2220); }
    K.b(1.9, .06, .54, 0, 1.98, 0, 0x38443f).b(.86, 1.8, .02, .62, .96, .38, 0x55665f, 0, .9, 0); },
  cabinet: K => { K.b(.9, 1.35, .55, 0, .675, 0, 0x6f6f66);
    for (let i = 0; i < 4; i++) K.b(.82, .29, .02, 0, .2 + i * .32, .28, 0x7b7b72).b(.2, .03, .03, 0, .24 + i * .32, .3, 0x25252a).b(.16, .06, .005, 0, .32 + i * .32, .291, 0xb6b29a);
    K.b(.8, .28, .5, .05, .52, .5, 0x7b7b72).b(.3, .02, .22, -.1, 1.36, .05, 0xb6b29a); },
  shelf: K => { K.b(.05, 2.0, .45, -.9, 1.0, 0, 0x3a3d40).b(.05, 2.0, .45, .9, 1.0, 0, 0x3a3d40).b(1.8, 2.0, .02, 0, 1.0, -.22, 0x2e3033);
    for (let i = 0; i < 5; i++) { K.b(1.8, .04, .45, 0, .08 + i * .46, 0, 0x45484b);
      for (let j = 0; j < 4; j++) { const hh = .14 + ((i * 3 + j * 5) % 4) * .06; if ((i + j) % 3) K.b(.2 + (j % 2) * .12, hh, .26, -.62 + j * .42, .1 + i * .46 + hh / 2, .02, [0x6a5a40, 0x34444e, 0x5a2c26, 0x7a7868][(i + j * 2) % 4]); } } },
  desk: K => { K.b(1.5, .05, .75, 0, .76, 0, 0x4a3c2c).b(.42, .6, .68, .5, .44, 0, 0x3e3226).b(.05, .74, .7, -.7, .37, 0, 0x3e3226).b(1.4, .4, .03, 0, .5, -.34, 0x3e3226);
    for (let i = 0; i < 3; i++) K.b(.36, .16, .02, .5, .22 + i * .2, .345, 0x4a3c2c).b(.12, .02, .02, .5, .22 + i * .2, .36, 0x1a1a1a);
    K.b(.5, .36, .04, -.2, 1.06, -.15, 0x18191b).b(.44, .3, .01, -.2, 1.06, -.128, 0x0a1014).b(.08, .12, .08, -.2, .84, -.15, 0x18191b).b(.24, .02, .16, -.2, .79, -.13, 0x18191b).b(.42, .02, .15, -.15, .795, .16, 0x242528).b(.26, .01, .34, .42, .79, .1, 0xb6b29a, 0, .3, 0); },
  chair: K => { K.b(.44, .05, .44, 0, .46, 0, 0x2c3238).b(.44, .5, .05, 0, .78, -.2, 0x2c3238, -.12, 0, 0);
    for (const a of [[-.19, -.19], [.19, -.19], [-.19, .19], [.19, .19]]) K.c(.018, .018, .46, a[0], .23, a[1], 0x6a6f72, 6);
    K.b(.03, .34, .03, -.19, .62, -.2, 0x6a6f72).b(.03, .34, .03, .19, .62, -.2, 0x6a6f72); },
  dumpster: K => { K.b(1.9, 1.1, 1.0, 0, .75, 0, 0x26402e).b(1.96, .08, 1.06, 0, 1.32, 0, 0x1c3023).b(1.94, .05, 1.1, 0, 1.4, -.04, 0x151719, -.12, 0, 0).b(1.92, .06, 1.02, 0, .22, 0, 0x151719);
    for (let i = 0; i < 4; i++) K.b(.06, 1.0, 1.04, -.72 + i * .48, .75, 0, 0x1f3526);
    for (const a of [[-.8, -.4], [.8, -.4], [-.8, .4], [.8, .4]]) K.c(.09, .09, .06, a[0], .09, a[1], 0x0a0a0a, 8, 0, 0, Math.PI / 2);
    K.b(.3, .06, .06, -1.0, 1.0, 0, 0x151719).b(.3, .06, .06, 1.0, 1.0, 0, 0x151719); },
  bench: K => { for (let i = 0; i < 4; i++) K.b(1.7, .04, .1, 0, .46, -.17 + i * .115, 0x4a3826); for (let i = 0; i < 3; i++) K.b(1.7, .1, .03, 0, .62 + i * .14, -.25 - i * .02, 0x4a3826);
    for (const s of [-.75, .75]) K.b(.06, .46, .46, s, .23, 0, 0x1c1e20).b(.06, .5, .06, s, .7, -.26, 0x1c1e20).b(.06, .04, .4, s, .64, .02, 0x1c1e20); },
  box: K => { K.b(.8, .8, .8, 0, .4, 0, 0x5a4630); for (const s of [-.4, .4]) K.b(.05, .84, .84, s, .4, 0, 0x3e3020).b(.84, .84, .05, 0, .4, s, 0x3e3020).b(.84, .05, .84, 0, .4 + s, 0, 0x3e3020);
    K.b(.5, .46, .5, .55, .23, .6, 0x6a5238, 0, .5, 0).b(.52, .04, .52, .55, .46, .6, 0x4a3a26, 0, .5, 0); },
  tyres: K => { for (let i = 0; i < 3; i++) K.g(new THREE.TorusGeometry(.26, .13, 7, 14), M((i % 2) * .05, .13 + i * .25, (i % 2) * -.04, Math.PI / 2, 0, 0), 0x0c0c0c);
    K.g(new THREE.TorusGeometry(.26, .13, 7, 14), M(.62, .36, .1, .25, .4, 0), 0x0c0c0c); },
  barrel: K => { K.c(.36, .36, 1.08, 0, .54, 0, 0xffffff, 14).c(.3, .3, .02, 0, 1.085, 0, 0x555555, 12).c(.04, .04, .04, .15, 1.11, .1, 0x222222, 6);
    for (const y of [.03, .36, .72, 1.06]) K.c(.375, .375, .045, 0, y, 0, 0xb0b0b0, 14); },
  hydrant: K => K.c(.11, .13, .6, 0, .3, 0, 0x7a1c16, 8).s(.115, 0, .6, 0, 0x7a1c16).c(.05, .05, .34, 0, .42, 0, 0x8a2a20, 6, 0, 0, Math.PI / 2).c(.16, .16, .05, 0, .03, 0, 0x5a1410, 8).c(.03, .03, .08, 0, .73, 0, 0x5a1410, 6),
  cone: K => K.g(new THREE.ConeGeometry(.16, .6, 10), M(0, .33, 0), 0xc4561a).c(.105, .13, .12, 0, .33, 0, 0xc8c8c0, 10).b(.4, .04, .4, 0, .02, 0, 0xa8480f),
  rail: K => { K.b(.05, .28, 3.0, 0, .62, 0, 0x8a8e90).b(.09, .08, 3.0, 0, .7, 0, 0x9a9ea0).b(.09, .08, 3.0, 0, .54, 0, 0x9a9ea0); for (const z of [-1.2, 0, 1.2]) K.b(.1, .8, .12, -.08, .4, z, 0x5a5e60); },
  pump: K => K.b(.9, .2, .6, 0, .1, 0, 0x55585a).b(.7, 1.5, .44, 0, .95, 0, 0x8a2a22).b(.74, .3, .48, 0, 1.75, 0, 0xb8b8b0).b(.5, .34, .02, 0, 1.3, .225, 0x0e1418).b(.5, .34, .02, 0, 1.3, -.225, 0x0e1418).b(.08, .3, .1, .4, 1.0, 0, 0x151515).seg(.02, .02, [.42, 1.1, 0], [.5, .4, .1], 0x101010, 5).seg(.02, .02, [.5, .4, .1], [.36, 1.5, 0], 0x101010, 5),
  roof: K => K.g(prism(), null, 0xffffff),
  barricade: K => { K.b(.2, 3.6, .22, -1.4, 1.8, 0, 0x2a2018).b(.2, 3.6, .22, 1.4, 1.8, 0, 0x2a2018).b(3.0, .22, .22, 0, 3.49, 0, 0x2a2018).b(3.0, .16, .26, 0, .08, 0, 0x2a2018);
    for (let i = 0; i < 6; i++) { const h = [3.3, 2.7, 3.4, 3.0, 3.38, 2.5][i]; K.b(.4, h, .05, -1.15 + i * .46, h / 2, (i % 2) * .05 - .02, [0x4a3826, 0x3e2e1e, 0x54402c][i % 3], 0, 0, (i % 3 - 1) * .02); }
    K.b(3.1, .26, .05, 0, 2.5, .09, 0x5c4630, 0, 0, .3).b(3.1, .26, .05, 0, 1.3, .09, 0x4c3a28, 0, 0, -.26).b(3.0, .24, .05, 0, .7, -.09, 0x5c4630, 0, 0, .08).b(2.9, .22, .05, 0, 2.1, -.09, 0x443424, 0, 0, -.12).b(1.1, .8, .02, .5, 1.75, .13, 0x4a3a30, 0, 0, .1);
    for (let i = 0; i < 8; i++) K.c(.012, .012, .03, -1.3 + i * .37, 1.3 - (i - 3.5) * .09, .12, 0x9a9a9a, 5, Math.PI / 2, 0, 0); }
};
function prism() { const g = new THREE.BufferGeometry(), A = [-.5, 0, -.5], B = [.5, 0, -.5], C = [0, 1, -.5], D = [-.5, 0, .5], E = [.5, 0, .5], F = [0, 1, .5];
  g.setAttribute('position', new THREE.Float32BufferAttribute([].concat(D, E, F, B, A, C, A, D, F, A, F, C, B, F, E, B, C, F, A, B, E, A, E, D), 3)); g.computeVertexNormals(); return g; }
Object.assign(KITS, {
  stair: K => { for (let i = 0; i < 20; i++) { const h = (i + 1) * .18; K.b(.3, h, 2.94, -2.85 + i * .3, h / 2, 0, i % 2 ? 0x77797b : 0x6b6d6f).b(.07, .035, 2.94, -2.965 + i * .3, h + .005, 0, 0xa0a2a4); }
    for (const s of [-1.44, 1.44]) K.g(new THREE.BoxGeometry(7, .07, .07), M(0, 2.78, s, 0, 0, Math.atan2(3.6, 6)), 0x1c1e20).g(new THREE.BoxGeometry(7, .5, .03), M(0, 2.3, s * 1.012, 0, 0, Math.atan2(3.6, 6)), 0x3a3c3e); },
  tlight: K => K.c(.09, .12, 5.4, 0, 2.7, 0, 0x26282a, 8).b(.1, .1, 3.2, 0, 5.3, 1.6, 0x26282a).b(.32, .95, .3, 0, 4.8, 3.0, 0x151515).s(.09, 0, 5.12, 3.16, 0x6a1410).s(.09, 0, 4.8, 3.16, 0x6a5a10).s(.09, 0, 4.48, 3.16, 0x104a1c).b(.4, .5, .3, 0, 1.2, 0, 0x303438).b(.36, .04, .34, 0, 5.3, 3.0, 0x151515),
  sign: K => K.c(.04, .04, 2.6, 0, 1.3, 0, 0x8a8e90, 6).b(.9, .9, .04, 0, 2.5, 0, 0x8a2a20, 0, 0, Math.PI / 4).b(.72, .72, .045, 0, 2.5, 0, 0xc0c0b8, 0, 0, Math.PI / 4).b(.5, .1, .05, 0, 2.5, 0, 0x8a2a20),
  pole: K => { K.c(.11, .15, 8, 0, 4, 0, 0x2a2118, 7).b(2.2, .12, .12, 0, 7.4, 0, 0x2a2118).b(1.6, .1, .1, 0, 6.8, 0, 0x2a2118).c(.24, .24, .7, .32, 6.1, 0, 0x4a4e52, 10);
    for (const s of [-.95, -.5, .5, .95]) K.c(.04, .05, .14, s, 7.53, 0, 0x8a8a80, 6); K.seg(.012, .012, [-.95, 7.6, 0], [-3.5, 6.6, 0], 0x101010, 4).seg(.012, .012, [.95, 7.6, 0], [3.5, 6.6, 0], 0x101010, 4); },
  bags: K => K.s(.34, 0, .24, 0, 0x0e0e10, 1, .8, 1).s(.3, .42, .2, .15, 0x121214, 1, .75, 1.1).s(.28, -.3, .19, .3, 0x0c0c0e, 1.1, .75, 1).s(.26, .1, .5, .2, 0x101012, 1, .8, 1).s(.06, 0, .5, 0, 0x101012).s(.05, .42, .42, .15, 0x101012),
  mailbox: K => K.b(.5, .8, .5, 0, .75, 0, 0x1c3a6a).c(.25, .25, .5, 0, 1.15, 0, 0x1c3a6a, 10, Math.PI / 2, 0, 0).b(.34, .05, .02, 0, .95, .255, 0x0a0a0a).b(.06, .35, .06, -.2, .18, -.2, 0x151719).b(.06, .35, .06, .2, .18, -.2, 0x151719).b(.06, .35, .06, -.2, .18, .2, 0x151719).b(.06, .35, .06, .2, .18, .2, 0x151719),
  bodybag: K => K.s(.3, 0, .15, 0, 0x16171a, 1, .5, 3.1).s(.2, 0, .2, .7, 0x1a1b1e, 1, .7, 1).b(.03, .02, 1.5, 0, .3, 0, 0x55575a).s(.3, .1, .01, .3, 0x3a0605, 1.6, .03, 1.2),
  tent: K => K.g(prism(), M(0, 0, 0, 0, 0, 0, 2.6, 1.5, 3.0), 0x4a5a3c).g(prism(), M(0, .06, 0, 0, 0, 0, 2.5, 1.46, 2.5), 0xaab6c6).b(.04, 1.55, .04, 0, .78, 1.5, 0x2a2118).b(.04, 1.55, .04, 0, .78, -1.5, 0x2a2118).b(1.6, .08, 2.6, 0, .04, 0, 0x2c3426),
  acunit: K => { K.b(1.6, 1.1, 1.2, 0, .6, 0, 0x7a7e80).b(1.7, .1, 1.3, 0, .05, 0, 0x3a3c3e).c(.42, .42, .06, 0, 1.17, 0, 0x151515, 14).c(.08, .08, .5, .5, .3, .7, 0x4a4e52, 8, Math.PI / 2, 0, 0); for (let i = 0; i < 7; i++) K.b(1.62, .03, .02, 0, .25 + i * .12, .61, 0x4a4e52); },
  truck: K => { const bd = 0xffffff, dk = 0x0b0b0d, gl = 0x121a20;
    K.b(2.3, 1.9, 2.0, 0, 1.75, 3.7, bd).b(2.1, .75, .05, 0, 2.1, 4.71, gl).b(2.32, .6, .9, 0, 2.15, 3.9, gl).b(2.34, .5, .2, 0, .9, 4.72, dk).b(1.2, .4, .06, 0, 1.3, 4.72, dk).b(2.2, .3, 9.6, 0, .85, 0, dk)
     .b(2.5, 2.8, 7.3, 0, 2.45, -1.15, 0xb4b4b0).b(2.52, .08, 7.32, 0, 1.06, -1.15, 0x55575a).b(2.52, 2.8, .04, 0, 2.45, -4.8, 0x8a8c8a).b(.04, 2.6, .04, 0, 2.45, -4.83, dk).c(.07, .07, 1.2, .9, 3.2, 2.6, 0x55575a, 8);
    for (const s of [-1, 1]) { K.b(.3, .16, .05, s * .8, 1.05, 4.73, 0xcfcfb8).b(.14, .3, .1, s * 1.25, 2.3, 4.5, dk);
      for (const z of [3.9, 1.6, -3.0, -4.0]) K.c(.5, .5, .32, s * 1.05, .5, z, 0x0a0a0a, 14, 0, 0, Math.PI / 2).c(.24, .24, .34, s * 1.05, .5, z, 0x6c6e70, 10, 0, 0, Math.PI / 2); } },
  gantry: K => { for (const s of [-16.4, 16.4]) K.c(.16, .2, 7, s, 3.5, 0, 0x55595c, 8).b(.6, .3, .6, s, .15, 0, 0x6a6c6e);
    K.b(33, .14, .14, 0, 6.9, 0, 0x55595c).b(33, .14, .14, 0, 6.1, 0, 0x55595c); for (let i = -8; i <= 8; i++) K.seg(.04, .04, [i * 2, 6.1, 0], [i * 2 + 1, 6.9, 0], 0x55595c, 4).seg(.04, .04, [i * 2 + 1, 6.9, 0], [i * 2 + 2, 6.1, 0], 0x55595c, 4);
    K.b(8, 2.6, .1, -7.5, 6.4, .14, 0x14402a).b(7.6, 2.2, .11, -7.5, 6.4, .15, 0x1c5236).b(5, .22, .12, -7.5, 6.9, .16, 0xc8c8c0).b(3.6, .22, .12, -8.2, 6.2, .16, 0xc8c8c0).b(6, 2.2, .1, 7, 6.2, .14, 0x14402a).b(4, .22, .12, 7, 6.5, .16, 0xc8c8c0).b(2.6, .22, .12, 6.3, 5.9, .16, 0xc8c8c0); },
  heli: K => { K.g(new THREE.SphereGeometry(1, 14, 10), M(0, 0, .6, 0, 0, 0, 1.3, 1.25, 2.6), 0x2c3327).g(new THREE.SphereGeometry(1, 12, 8), M(0, .15, 2.2, 0, 0, 0, 1.1, .85, 1.1), 0x10161a)
     .g(q4(.12, .4, 5), M(0, .35, -4.3, -Math.PI / 2, 0, 0), 0x2c3327).b(.1, 1.5, .9, 0, 1.0, -6.6, 0x2c3327).c(.2, .26, .6, 0, 1.45, .4, 0x1c1e20, 8).b(2.4, .5, 1.6, 0, .1, .4, 0x262c22);
    for (const s of [-1.1, 1.1]) K.b(.1, .1, 4.2, s, -1.5, .6, 0x151515).seg(.04, .04, [s * .8, -.9, 1.6], [s, -1.5, 1.6], 0x151515, 5).seg(.04, .04, [s * .8, -.9, -.4], [s, -1.5, -.4], 0x151515, 5).b(.05, .5, 1.2, s * 1.28, .2, .5, 0x10161a); },
  pool: K => K.c(1, 1, .01, 0, 0, 0, 0x2a0403, 14).c(.45, .45, .011, .9, 0, .5, 0x2a0403, 10).c(.3, .3, .011, -.8, 0, -.7, 0x2a0403, 8).b(.25, .011, 1.6, .3, 0, 1.4, 0x2a0403, 0, .3, 0),
  hang: K => { K.c(.012, .012, 1.0, 0, 3.1, 0, 0x2a2118, 5).s(.25, 0, 1.72, 0, 0x1c1916, 1, 2.7, .95).s(.13, 0, 2.5, .02, 0x1c1916, 1, 1.1, 1).c(.26, .2, .05, 0, 2.2, 0, 0x2a2118, 10).c(.25, .22, .05, 0, 1.5, 0, 0x2a2118, 10).c(.16, .1, .05, 0, 1.12, 0, 0x2a2118, 10)
     .s(.1, .06, 1.02, 0, 0x4a5244, 1, 1.6, 1).s(.1, -.07, .98, .02, 0x4a5244, 1, 1.6, 1).s(.26, 0, 1.6, .03, 0x3a0605, .96, 1.2, 1); for (let i = 0; i < 4; i++) K.b(.012, .25 + i * .08, .012, -.1 + i * .07, .78 - i * .04, .05, 0x3a0605); },
  gen: K => { K.b(1.6, .1, .95, 0, .19, 0, 0x26282a).b(1.3, .62, .8, 0, .56, 0, 0x8a6a14).b(.52, .56, .74, .36, .6, 0, 0x34373a).c(.3, .3, .74, -.3, 1.06, 0, 0x6a1c16, 12, 0, 0, Math.PI / 2).c(.06, .06, .08, -.3, 1.38, 0, 0x151515, 8)
     .c(.045, .045, .7, .5, 1.2, .22, 0x2a2c2e, 8).c(.07, .07, .16, .5, 1.6, .22, 0x151515, 8).b(.46, .3, .04, -.3, .58, .41, 0x121416).b(.1, .06, .05, -.42, .62, .44, 0x8a2a20).b(.1, .06, .05, -.2, .62, .44, 0xc8c8c0)
     .b(1.7, .05, .05, 0, .98, .47, 0x26282a).b(1.7, .05, .05, 0, .98, -.47, 0x26282a); for (const a of [[-.82, .47], [.82, .47], [-.82, -.47], [.82, -.47]]) K.b(.05, .84, .05, a[0], .58, a[1], 0x26282a);
    for (const a of [[-.55, .5], [.55, .5], [-.55, -.5], [.55, -.5]]) K.c(.15, .15, .1, a[0], .15, a[1], 0x0a0a0a, 10, Math.PI / 2, 0, 0); for (let i = 0; i < 5; i++) K.b(.5, .03, .02, .36, .42 + i * .08, .376, 0x151515); },
  case: K => K.b(.95, .4, .58, 0, .22, 0, 0x39432a).b(.99, .07, .62, 0, .42, 0, 0x2a3220).b(.32, .03, .04, 0, .475, 0, 0x151515).b(.06, .1, .02, -.3, .36, .3, 0x9a9a90).b(.06, .1, .02, .3, .36, .3, 0x9a9a90).b(.22, .07, .012, 0, .22, .296, 0xc8c8c0).b(.07, .22, .012, 0, .22, .297, 0xc8c8c0).b(1.0, .04, .63, 0, .03, 0, 0x2a3220),
  stack: K => { const cr = (sz, x, y, z, ry, col) => { K.b(sz, sz, sz, x, y, z, col, 0, ry, 0); for (const e of [-1, 1]) K.b(sz * 1.04, sz * .09, sz * 1.04, x, y + e * sz * .44, z, 0x3a2c1c, 0, ry, 0).b(sz * .09, sz * 1.02, sz * 1.04, x + Math.cos(ry) * e * sz * .46, y, z - Math.sin(ry) * e * sz * .46, 0x3a2c1c, 0, ry, 0); };
    cr(.9, -.3, .45, 0, .1, 0x5a4630); cr(.8, .62, .4, .1, -.3, 0x66503a); cr(.7, -.1, 1.25, .05, .5, 0x54402c); K.b(.5, .3, .4, .7, .95, .1, 0x39432a, 0, .4, 0).b(1.0, .02, .7, .5, .82, .1, 0x2c3426, .05, -.3, .04); },
  pallet: K => { for (let i = 0; i < 5; i++) K.b(1.2, .025, .15, 0, .14, -.42 + i * .21, 0x6a5238); for (const z of [-.42, 0, .42]) K.b(1.2, .1, .1, 0, .07, z, 0x54402c);
    K.b(.5, .4, .5, -.3, .36, .1, 0x7a6a50).b(.45, .35, .45, .28, .33, -.12, 0x6a5a44).s(.26, .3, .3, .32, 0x8a8068, 1.3, .6, 1).s(.26, -.25, .68, .1, 0x8a8068, 1.3, .55, 1); },
  sandbag: K => { for (let r = 0; r < 3; r++) for (let i = 0; i < 5 - r; i++) K.s(.24, -1.0 + i * .5 + r * .25, .14 + r * .25, (r % 2) * .04, r % 2 ? 0x6a5e44 : 0x74684c, 1.25, .62, 1); },
  vending: K => K.b(.95, 1.95, .7, 0, .98, 0, 0x1c2a4a).b(.62, 1.15, .02, -.12, 1.2, .355, 0x0a0e14).b(.2, .5, .02, .33, 1.3, .355, 0x2a2c30).b(.6, .2, .02, -.12, .32, .355, 0x0e1014).b(.99, .06, .74, 0, 1.97, 0, 0x121a2e).b(.99, .1, .74, 0, .05, 0, 0x121a2e).b(.5, .012, .01, -.12, 1.5, .37, 0x4a5a8a, 0, 0, .6).b(.3, .012, .01, -.2, 1.0, .37, 0x4a5a8a, 0, 0, -.8),
  ladder: K => { for (const sx of [-.22, .22]) K.seg(.025, .025, [sx, 0, .55], [sx, 3.2, -.12], 0x7a7e80, 6); for (let i = 1; i < 10; i++) K.c(.016, .016, .44, 0, i * .32, .55 - i * .067, 0x8a8e90, 6, 0, 0, Math.PI / 2); },
  cpipe: K => K.c(.07, .07, 3, 0, 0, 0, 0x4a4f52, 10, 0, 0, Math.PI / 2).c(.035, .035, 3, 0, .02, .22, 0x6a3a2a, 8, 0, 0, Math.PI / 2).c(.025, .025, 3, 0, -.03, -.17, 0x3a3c3e, 8, 0, 0, Math.PI / 2)
    .b(.06, .2, .56, -1.1, .08, 0, 0x2a2c2e).b(.06, .2, .56, 1.1, .08, 0, 0x2a2c2e).c(.095, .095, .08, .4, 0, 0, 0x33383a, 10, 0, 0, Math.PI / 2).c(.07, .07, .03, -.5, -.14, 0, 0x7a2018, 8).c(.012, .012, .12, -.5, -.08, 0, 0x2a2a2a, 6),
  chain: K => { for (const [x, z, h] of [[0, 0, 1.7], [.35, .2, 1.1], [-.3, .25, .8]]) for (let i = 0; i < h / .09; i++) K.b(.03, .07, .012, x, -i * .09, z, 0x2c2c2c, 0, i % 2 ? Math.PI / 2 : 0);
    return K.b(.02, .16, .02, 0, -1.78, 0, 0x3a3a3a).b(.1, .02, .02, .04, -1.86, 0, 0x3a3a3a).b(.02, .08, .02, .09, -1.82, 0, 0x3a3a3a).s(.11, .35, -1.25, .2, 0x3a0a08, 1, 1.6, 1); },
  bones: K => K.s(.1, 0, .09, 0, 0xc4bca2, 1, .95, 1.1).b(.1, .05, .08, 0, .03, .07, 0xb4ac92).b(.03, .03, .01, -.035, .1, .1, 0x0a0a0a).b(.03, .03, .01, .035, .1, .1, 0x0a0a0a)
    .seg(.018, .018, [.25, .02, -.1], [.6, .02, .1], 0xc4bca2).seg(.018, .018, [-.2, .02, .3], [-.5, .02, .05], 0xb8b096).seg(.014, .014, [.1, .02, .4], [.4, .02, .45], 0xc4bca2)
    .s(.03, .25, .025, -.1, 0xc4bca2).s(.03, .6, .025, .1, 0xc4bca2).b(.3, .012, .26, -.3, .006, -.3, 0x2a0605, 0, .4),
  papers: K => { for (let i = 0; i < 7; i++) K.b(.21, .003, .29, Math.sin(i * 2.4) * .6, .004 + i * .001, Math.cos(i * 1.7) * .6, i % 3 ? 0xb8b4a4 : 0x8a8676, 0, i * 1.1); return K; },
  candle: K => K.c(.03, .034, .16, 0, .08, 0, 0xd8d0b8, 8).c(.026, .03, .1, .1, .05, .06, 0xd0c8b0, 8).c(.028, .03, .22, -.07, .11, .08, 0xd8d0b8, 8).c(.12, .13, .01, 0, .005, .04, 0xb8b09a, 10),
  grave: K => K.b(.09, 1.1, .07, 0, .55, 0, 0x4a3a28, 0, 0, .06).b(.6, .09, .07, 0, .8, 0, 0x4a3a28, 0, 0, .06).s(.5, 0, 0, .7, 0x3a2c20, 1, .3, 1.7).b(.3, .01, .2, 0, .16, .5, 0x2a0605),
  stake: K => K.c(.03, .045, 1.9, 0, .95, 0, 0x3a2c1e, 6).s(.1, 0, 1.92, 0, 0xc4bca2, 1, .95, 1.1).b(.1, .05, .08, 0, 1.85, .06, 0xb4ac92).b(.03, .03, .01, -.035, 1.93, .1, 0x0a0a0a).b(.03, .03, .01, .035, 1.93, .1, 0x0a0a0a).c(.035, .04, .5, 0, 1.55, 0, 0x2a0605, 6),
  rotor: K => K.b(11, .04, .34, 0, 0, 0, 0x151515).b(.34, .04, 11, 0, 0, 0, 0x151515).c(.16, .16, .2, 0, 0, 0, 0x2a2c2e, 8)
});
const METAL = { car: 1, van: 1, lamp: 1, rail: 1, dumpster: 1, locker: 1, barrel: 1, pump: 1, truck: 1, tlight: 1, gantry: 1, acunit: 1, mailbox: 1, heli: 1 }, NOSHADOW = { drift: 1, deb: 1, pool: 1, pineL: 1, papers: 1 };
function kitGeo(name) { if (!KGEO[name]) { const K = Kit(); KITS[name](K); const g = K.done(); g.userData.keep = true; KGEO[name] = g; } return KGEO[name]; }
function wallGeo(kind) {
  const key = 'w_' + kind; if (KGEO[key]) return KGEO[key];
  const K = Kit(), T = TILE, h = WALL_H, y0 = -h / 2, cross = (w, hh, y, col) => { K.b(T + w, hh, T, 0, y, 0, col).b(T, hh, T + w, 0, y, 0, col); };
  K.g(new THREE.BoxGeometry(T, h, T, 1, 4, 1), null, 0xffffff);
  if (kind === 'in') { cross(.1, .2, y0 + .1, 0x5a564c); cross(.05, .07, y0 + 1.02, 0x8a877c); cross(.12, .14, h / 2 - .07, 0x8f8c80); }
  if (kind === 'rib') { cross(.16, .5, y0 + .25, 0x858585); cross(.22, .24, h / 2 - .12, 0x9a9a9a); K.b(.55, h, T + .18, 0, 0, 0, 0xb4b4b4).b(T + .18, h, .55, 0, 0, 0, 0xb4b4b4); }
  if (kind === 'plank') { cross(.14, .24, y0 + .12, 0x5a4a3a); cross(.14, .24, h / 2 - .12, 0x5a4a3a); cross(.07, .13, .1, 0x74624c); K.b(.26, h, T + .13, 0, 0, 0, 0x64523e).b(T + .13, h, .26, 0, 0, 0, 0x64523e); }
  if (kind === 'brick') { cross(.14, .62, y0 + .31, 0x7c7e80); cross(.18, .28, h / 2 - .14, 0x8e9092); K.b(.7, h, T + .1, 0, 0, 0, 0xc4c0bc).b(T + .1, h, .7, 0, 0, 0, 0xc4c0bc); }
  if (kind === 'facade' || kind === 'fwall') cross(.32, .2, y0 + .1, 0x9a9c9e);
  const g = K.done(), p = g.attributes.position, c = g.attributes.color;
  for (let i = 0; i < p.count; i++) { const y = p.getY(i), f = kind === 'facade' || kind === 'fwall' ? 1 : y < -.9 ? .45 + .55 * (y + 1.8) / .9 : y > .9 ? 1 - .4 * (y - .9) / .9 : 1; c.setXYZ(i, c.getX(i) * f, c.getY(i) * f, c.getZ(i) * f); }
  g.userData.keep = true; return KGEO[key] = g;
}
const put = (kind, x, y, z, ry, sx, sy, sz, col, rx, rz) => { (instQ[kind] = instQ[kind] || []).push([M(x, y + PY, z, rx, ry, rz, sx, sy, sz), col]); };
const pushW = (mat, geo, x, y, z) => { const k = mat + '|' + geo; (wallQ[k] = wallQ[k] || []).push([x, y, z]); };
function glow(x, y, z, sx, sy, sz, hex, ry) { glowQ.push([M(x, y + PY, z, 0, ry, 0, sx, sy, sz), hex]); return glowQ.length - 1; }
function spot(x, y, z, col, base, range, mode, gi) {
  const s = { x, y: y + PY, z, col: new THREE.Color(col), base, range, mode: mode || 0, ph: LR() * 99, v: 1, gi: gi === undefined ? -1 : gi, gc: null, a: 0, pl: -1, d: 0 };
  if (s.gi >= 0) s.gc = new THREE.Color(glowQ[s.gi][1]).convertSRGBToLinear();
  lightSpots.push(s); return s;
}

// ---------------------------------------------------------------- level textures
function dual(size, draw) { return [canvasTex(size, (g, s) => draw(g, s, false)), canvasTex(size, (g, s) => draw(g, s, true), false)]; }
const gy = v => { v = Math.max(0, Math.min(255, v | 0)); return `rgb(${v},${v},${v})`; };
function streaks(g, s, n, col) { for (let i = 0; i < n; i++) { const x = Math.random() * s, y = Math.random() * s * .6, h = rnd(50, 240), gr = g.createLinearGradient(0, y, 0, y + h);
  gr.addColorStop(0, `rgba(${col},.5)`); gr.addColorStop(1, `rgba(${col},0)`); g.fillStyle = gr; g.fillRect(x, y, rnd(2, 8), h); } }
const plankDraw = (hz, base) => (g, s, b) => {
  const n = 8, w = s / n; g.fillStyle = b ? '#000' : '#0c0906'; g.fillRect(0, 0, s, s);
  for (let i = 0; i < n; i++) { const v = rnd(.75, 1.12);
    g.fillStyle = b ? gy(v * 175) : `rgb(${(base[0] * v) | 0},${(base[1] * v) | 0},${(base[2] * v) | 0})`;
    if (hz) g.fillRect(0, i * w + 2, s, w - 4); else g.fillRect(i * w + 2, 0, w - 4, s);
    if (b) continue;
    g.strokeStyle = 'rgba(0,0,0,.28)'; g.lineWidth = 1;
    for (let k = 0; k < 12; k++) { const p = i * w + rnd(4, w - 4); g.beginPath(); if (hz) { g.moveTo(0, p); g.bezierCurveTo(s * .3, p + rnd(-4, 4), s * .6, p + rnd(-4, 4), s, p); } else { g.moveTo(p, 0); g.bezierCurveTo(p + rnd(-4, 4), s * .3, p + rnd(-4, 4), s * .6, p, s); } g.stroke(); }
    for (let k = 0; k < 2; k++) { g.fillStyle = 'rgba(15,10,6,.7)'; g.beginPath(); g.ellipse(hz ? rnd(0, s) : i * w + w / 2 + rnd(-8, 8), hz ? i * w + w / 2 + rnd(-8, 8) : rnd(0, s), rnd(3, 6), rnd(5, 9), 0, 0, 7); g.fill(); } }
  if (!b) { blotch(g, s, 24, '10,8,5', 20, 80, .4); grainFx(g, s, 26); }
};
const TEXDEF = {
  snow: (g, s, b) => { g.fillStyle = b ? '#808080' : '#a4aebe'; g.fillRect(0, 0, s, s);
    if (b) { blotch(g, s, 50, '230,230,230', 20, 70, .5); blotch(g, s, 50, '30,30,30', 15, 60, .5); grainFx(g, s, 60); }
    else { blotch(g, s, 40, '196,206,222', 20, 90, .5); blotch(g, s, 30, '104,118,146', 20, 80, .35); blotch(g, s, 12, '60,60,56', 3, 10, .4); grainFx(g, s, 16); } },
  paper: (g, s, b) => { g.fillStyle = b ? '#888' : '#96883f'; g.fillRect(0, 0, s, s);
    for (let x = 0; x < s; x += 32) { g.fillStyle = b ? 'rgba(255,255,255,.14)' : 'rgba(116,104,46,.6)'; g.fillRect(x, 0, 3, s); g.fillStyle = b ? 'rgba(0,0,0,.1)' : 'rgba(170,158,84,.5)'; g.fillRect(x + 16, 0, 1, s);
      if (!b) for (let y = 8; y < s; y += 32) { g.strokeStyle = 'rgba(112,98,42,.75)'; g.lineWidth = 1.5; g.beginPath(); g.moveTo(x + 9, y + 8); g.lineTo(x + 17, y); g.lineTo(x + 25, y + 8); g.lineTo(x + 17, y + 16); g.closePath(); g.stroke(); } }
    if (b) { grainFx(g, s, 30); return; }
    blotch(g, s, 26, '50,42,10', 20, 100, .38); blotch(g, s, 10, '150,140,80', 20, 60, .25); streaks(g, s, 16, '40,32,8');
    const gr = g.createLinearGradient(0, s * .7, 0, s); gr.addColorStop(0, 'rgba(20,16,4,0)'); gr.addColorStop(1, 'rgba(20,16,4,.7)'); g.fillStyle = gr; g.fillRect(0, s * .7, s, s * .3); grainFx(g, s, 22); },
  carpet: (g, s, b) => { g.fillStyle = b ? '#808080' : '#6a6032'; g.fillRect(0, 0, s, s); if (b) { grainFx(g, s, 120); return; }
    blotch(g, s, 40, '40,34,12', 20, 90, .45); blotch(g, s, 16, '110,100,56', 10, 50, .3); blotch(g, s, 6, '24,20,10', 30, 90, .6); grainFx(g, s, 44); },
  ctile: (g, s, b) => { g.fillStyle = b ? '#b0b0b0' : '#8b886a'; g.fillRect(0, 0, s, s); g.strokeStyle = b ? '#202020' : '#3a382a'; g.lineWidth = 5;
    for (let i = 0; i <= 2; i++) { g.beginPath(); g.moveTo(i * s / 2, 0); g.lineTo(i * s / 2, s); g.moveTo(0, i * s / 2); g.lineTo(s, i * s / 2); g.stroke(); }
    if (b) { grainFx(g, s, 50); return; } for (let i = 0; i < 900; i++) { g.fillStyle = 'rgba(40,38,26,.5)'; g.fillRect(Math.random() * s, Math.random() * s, 2, 2); }
    blotch(g, s, 10, '70,48,16', 30, 110, .5); blotch(g, s, 20, '30,28,20', 20, 60, .3); grainFx(g, s, 22); },
  concrete: (g, s, b) => { g.fillStyle = b ? '#a0a0a0' : '#54575a'; g.fillRect(0, 0, s, s); g.fillStyle = b ? '#303030' : '#26282a'; g.fillRect(s / 2 - 3, 0, 6, s); g.fillRect(0, s * .5 - 2, s, 4);
    for (const x of [.12, .38, .62, .88]) for (const y of [.14, .86]) { g.beginPath(); g.arc(x * s, y * s, 6, 0, 7); g.fill(); }
    if (b) { cracks(g, s, 6, '#101010'); grainFx(g, s, 70); return; }
    blotch(g, s, 40, '30,32,34', 20, 90, .4); blotch(g, s, 20, '120,122,124', 10, 60, .2); streaks(g, s, 30, '24,22,18'); cracks(g, s, 8, 'rgba(12,12,12,.8)');
    for (let i = 0; i < 4; i++) { g.strokeStyle = ['rgba(120,30,26,.5)', 'rgba(40,70,110,.45)', 'rgba(150,150,140,.4)', 'rgba(20,20,20,.6)'][i]; g.lineWidth = rnd(3, 7); let x = rnd(40, s - 160), y = rnd(s * .35, s * .8); g.beginPath(); g.moveTo(x, y);
      for (let k = 0; k < 6; k++) { x += rnd(10, 40); y += rnd(-40, 40); g.quadraticCurveTo(x - 20, y + rnd(-30, 30), x, y); } g.stroke(); }
    const gr = g.createLinearGradient(0, s * .8, 0, s); gr.addColorStop(0, 'rgba(0,0,0,0)'); gr.addColorStop(1, 'rgba(0,0,0,.7)'); g.fillStyle = gr; g.fillRect(0, s * .8, s, s * .2); grainFx(g, s, 30); },
  asphalt: (g, s, b) => { g.fillStyle = b ? '#808080' : '#1c1d1f'; g.fillRect(0, 0, s, s); if (b) { cracks(g, s, 10, '#000'); grainFx(g, s, 110); return; }
    blotch(g, s, 40, '44,45,48', 20, 90, .4); blotch(g, s, 30, '8,8,9', 20, 80, .5); for (let i = 0; i < 1500; i++) { g.fillStyle = `rgba(${Math.random() < .5 ? '90,90,92' : '0,0,0'},.35)`; g.fillRect(Math.random() * s, Math.random() * s, 2, 2); }
    cracks(g, s, 10, 'rgba(0,0,0,.9)'); g.strokeStyle = 'rgba(6,6,6,.8)'; g.lineWidth = 4; for (let i = 0; i < 3; i++) { let x = Math.random() * s, y = 0; g.beginPath(); g.moveTo(x, y); for (let k = 0; k < 8; k++) { x += rnd(-30, 30); y += s / 8; g.lineTo(x, y); } g.stroke(); }
    blotch(g, s, 3, '60,6,5', 20, 50, .5); grainFx(g, s, 26); },
  sidewalk: (g, s, b) => { g.fillStyle = b ? '#a8a8a8' : '#454643'; g.fillRect(0, 0, s, s); g.strokeStyle = b ? '#282828' : '#1a1b19'; g.lineWidth = 5;
    for (let i = 0; i <= 2; i++) { g.beginPath(); g.moveTo(i * s / 2, 0); g.lineTo(i * s / 2, s); g.moveTo(0, i * s / 2); g.lineTo(s, i * s / 2); g.stroke(); }
    if (b) { cracks(g, s, 6, '#101010'); grainFx(g, s, 70); return; }
    blotch(g, s, 40, '24,24,22', 20, 80, .45); blotch(g, s, 14, '100,100,96', 10, 40, .2); for (let i = 0; i < 30; i++) { g.fillStyle = 'rgba(14,14,13,.7)'; g.beginPath(); g.arc(Math.random() * s, Math.random() * s, rnd(2, 5), 0, 7); g.fill(); }
    cracks(g, s, 7, 'rgba(8,8,8,.85)'); blotch(g, s, 3, '70,6,5', 20, 50, .5); grainFx(g, s, 30); },
  dirt: (g, s, b) => { g.fillStyle = b ? '#808080' : '#27221b'; g.fillRect(0, 0, s, s); if (b) { blotch(g, s, 60, '40,40,40', 6, 30, .5); blotch(g, s, 50, '210,210,210', 3, 12, .5); grainFx(g, s, 90); return; }
    blotch(g, s, 60, '14,12,9', 15, 70, .55); blotch(g, s, 40, '70,60,44', 5, 30, .3); for (let i = 0; i < 400; i++) { g.fillStyle = `rgba(${rnd(60, 110) | 0},${rnd(55, 95) | 0},${rnd(45, 75) | 0},.6)`; g.fillRect(Math.random() * s, Math.random() * s, rnd(1, 4), rnd(1, 3)); }
    g.strokeStyle = 'rgba(70,66,36,.5)'; for (let i = 0; i < 200; i++) { const x = Math.random() * s, y = Math.random() * s; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-3, 3), y - rnd(3, 8)); g.stroke(); } grainFx(g, s, 40); },
  brick: (g, s, b) => { g.fillStyle = b ? '#505050' : '#211c19'; g.fillRect(0, 0, s, s); const bh = s / 14, bw = s / 5;
    for (let y = 0; y < 14; y++) for (let x = -1; x < 5; x++) { const v = rnd(.7, 1.1); g.fillStyle = b ? gy(v * 190) : `rgb(${(92 * v) | 0},${(46 * v) | 0},${(36 * v) | 0})`; g.fillRect(x * bw + (y % 2) * bw / 2 + 2, y * bh + 2, bw - 4, bh - 4); }
    if (b) { grainFx(g, s, 40); return; }
    blotch(g, s, 40, '16,13,11', 20, 90, .5); blotch(g, s, 12, '130,120,110', 10, 40, .15); streaks(g, s, 22, '14,12,10');
    const gr = g.createLinearGradient(0, s * .75, 0, s); gr.addColorStop(0, 'rgba(0,0,0,0)'); gr.addColorStop(1, 'rgba(0,0,0,.7)'); g.fillStyle = gr; g.fillRect(0, s * .75, s, s * .25); grainFx(g, s, 30); },
  facade: (g, s, b) => { g.fillStyle = b ? '#a8a8a8' : '#383a3e'; g.fillRect(0, 0, s, s);
    if (!b) { blotch(g, s, 40, '18,18,20', 20, 90, .45); streaks(g, s, 26, '12,12,12'); }
    for (const wp of [.08, .57]) { const x = wp * s, y = .18 * s, w = .35 * s, h = .58 * s;
      g.fillStyle = b ? '#e0e0e0' : '#54575b'; g.fillRect(x - 9, y - 9, w + 18, h + 18);
      g.fillStyle = b ? '#181818' : (Math.random() < .1 ? '#3c331c' : '#06080b'); g.fillRect(x, y, w, h);
      if (!b) { g.fillStyle = '#3d4044'; g.fillRect(x + w / 2 - 3, y, 6, h); g.fillRect(x, y + h * .45, w, 5);
        g.strokeStyle = 'rgba(140,160,170,.35)'; g.lineWidth = 1; for (let k = 0; k < 6; k++) { g.beginPath(); g.moveTo(x + rnd(0, w), y + rnd(0, h)); g.lineTo(x + rnd(0, w), y + rnd(0, h)); g.stroke(); }
        if (Math.random() < .3) { g.fillStyle = '#2c241a'; g.fillRect(x - 5, y + h * .28, w + 10, h * .14); g.fillRect(x - 5, y + h * .62, w + 10, h * .12); } }
      g.fillStyle = b ? '#ffffff' : '#63666b'; g.fillRect(x - 15, y + h + 9, w + 30, 11); }
    if (!b) grainFx(g, s, 24); }
};
function texMat(name) {
  if (MAT[name]) return MAT[name];
  const bump = MAT._bump || (MAT._bump = bumpTex());
  const mk = (map, o, bm) => new THREE.MeshStandardMaterial(Object.assign({ map, bumpMap: bm || bump, bumpScale: bm ? .09 : .045, roughness: .92, metalness: 0, vertexColors: true }, o || {}));
  const d2 = (n, size, o) => { const t = dual(size || 512, TEXDEF[n]); return mk(t[0], o, t[1]); };
  let m;
  if (name === 'wallA' || name === 'wallB') m = mk(wallTex(name === 'wallB' ? 1 : 0));
  else if (name === 'floor') m = mk(canvasTex(512, (g, s) => { const n = 4, t = s / n;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { g.fillStyle = (i + j) % 2 ? '#5a5c53' : '#484a44'; g.fillRect(i * t, j * t, t, t); }
    g.strokeStyle = '#191a17'; g.lineWidth = 3; for (let i = 0; i <= n; i++) { g.beginPath(); g.moveTo(i * t, 0); g.lineTo(i * t, s); g.moveTo(0, i * t); g.lineTo(s, i * t); g.stroke(); }
    blotch(g, s, 30, '15,14,10', 20, 80, .45); blotch(g, s, 4, '85,8,6', 20, 60, .55); cracks(g, s, 5, 'rgba(10,10,8,.8)'); grainFx(g, s, 30); }), { roughness: .62 });
  else if (name === 'ceil') m = mk(canvasTex(512, (g, s) => { g.fillStyle = '#5b5b53'; g.fillRect(0, 0, s, s); g.strokeStyle = '#2a2a25'; g.lineWidth = 4;
    g.strokeRect(0, 0, s / 2, s / 2); g.strokeRect(s / 2, 0, s / 2, s / 2); g.strokeRect(0, s / 2, s / 2, s / 2); g.strokeRect(s / 2, s / 2, s / 2, s / 2);
    blotch(g, s, 12, '60,42,18', 30, 100, .5); blotch(g, s, 20, '20,20,18', 20, 60, .4); grainFx(g, s, 26); }));
  else if (name === 'ground') m = mk(canvasTex(512, (g, s) => { g.fillStyle = '#2b3023'; g.fillRect(0, 0, s, s); blotch(g, s, 70, '18,16,10', 15, 70, .6); blotch(g, s, 40, '60,70,40', 5, 25, .3);
    g.strokeStyle = 'rgba(70,84,44,.5)'; for (let i = 0; i < 500; i++) { const x = Math.random() * s, y = Math.random() * s; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-3, 3), y - rnd(3, 9)); g.stroke(); } grainFx(g, s, 46); }), { roughness: 1 });
  else if (name === 'plank') { const t = dual(512, plankDraw(false, [74, 56, 38])); m = mk(t[0], { roughness: .85 }, t[1]); }
  else if (name === 'woodfloor') { const t = dual(512, plankDraw(true, [62, 46, 30])); m = mk(t[0], { roughness: .7 }, t[1]); }
  else if (name === 'snow') m = d2('snow', 512, { roughness: .8 });
  else if (name === 'asphalt') m = d2('asphalt', 512, { roughness: .82 });
  else if (name === 'carpet') m = d2('carpet', 256, { roughness: 1 });
  else m = d2(name);
  return MAT[name] = m;
}
const UVS = { floor: 3, woodfloor: 3, ctile: 3, ceil: 3, sidewalk: 3, carpet: 4, snow: 10, asphalt: 7, ground: 6, dirt: 6 };
function initLevelMats() {
  const bump = MAT._bump = bumpTex();
  const grime = canvasTex(256, (g, s) => { g.fillStyle = '#d0d0d0'; g.fillRect(0, 0, s, s); blotch(g, s, 40, '60,56,50', 8, 50, .4); blotch(g, s, 20, '255,255,255', 6, 30, .3); streaks(g, s, 14, '40,36,30'); grainFx(g, s, 40); });
  MAT.vc = new THREE.MeshStandardMaterial({ map: grime, bumpMap: bump, bumpScale: .02, roughness: .88, metalness: 0, vertexColors: true });
  MAT.vcM = new THREE.MeshStandardMaterial({ map: grime, bumpMap: bump, bumpScale: .012, roughness: .5, metalness: .35, vertexColors: true });
  MAT.glow = new THREE.MeshBasicMaterial({ color: 0xffffff });
  MAT.beacon = new THREE.MeshBasicMaterial({ color: 0x50ff90, transparent: true, opacity: .4, depthWrite: false, side: THREE.DoubleSide });
  MAT.wood = new THREE.MeshStandardMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#3a2c1c'; g.fillRect(0, 0, s, s); for (let i = 0; i < 40; i++) { g.fillStyle = `rgba(${rnd(20, 90) | 0},${rnd(15, 60) | 0},20,.35)`; g.fillRect(0, Math.random() * s, s, rnd(1, 4)); } grainFx(g, s, 30); }), bumpMap: bump, bumpScale: .03, roughness: .9 });
  MAT.metal = new THREE.MeshStandardMaterial({ color: 0x23272a, metalness: .85, roughness: .42 });
  MAT.olive = new THREE.MeshStandardMaterial({ color: 0x39432a, metalness: .3, roughness: .7 });
  MAT.white = new THREE.MeshStandardMaterial({ color: 0x9a9c94, metalness: .2, roughness: .6 });
  for (const m of [MAT.olive, MAT.white]) m.color.convertSRGBToLinear();
  KGEO.glowBox = new THREE.BoxGeometry(1, 1, 1); KGEO.glowBox.userData.keep = true;
  hemi = new THREE.HemisphereLight(0x31405c, 0x0a0a08, .22); scene.add(hemi);
  sun = new THREE.DirectionalLight(0x8fa8d8, 0); sun.position.set(40, 80, -30); scene.add(sun);
  for (let i = 0; i < 8; i++) { const l = new THREE.PointLight(0xffffff, 0, 12, 1.8); scene.add(l); pool.push({ l, spot: null }); }
  // sky: stars + moon, and weather particles that follow the camera
  skyGroup = new THREE.Group(); scene.add(skyGroup);
  const sp = []; for (let i = 0; i < 600; i++) { const a = Math.random() * 6.283, e = Math.asin(Math.random() * .95 + .04); sp.push(Math.cos(a) * Math.cos(e) * 170, Math.sin(e) * 170, Math.sin(a) * Math.cos(e) * 170); }
  const sg = new THREE.BufferGeometry(); sg.setAttribute('position', new THREE.Float32BufferAttribute(sp, 3));
  const stars = new THREE.Points(sg, new THREE.PointsMaterial({ color: 0xaab4cc, size: 1.5, sizeAttenuation: false, fog: false, transparent: true, opacity: .7 })); stars.frustumCulled = false; skyGroup.add(stars);
  const moon = new THREE.Mesh(new THREE.SphereGeometry(6, 18, 14), new THREE.MeshBasicMaterial({ color: 0xbfc8d8, fog: false })); moon.position.set(70, 120, -90); skyGroup.add(moon); skyGroup.userData = { stars, moon };
  const wp = new Float32Array(420 * 3); for (let i = 0; i < 420; i++) { wp[i * 3] = rnd(-12, 12); wp[i * 3 + 1] = rnd(0, 12); wp[i * 3 + 2] = rnd(-12, 12); }
  const wg = new THREE.BufferGeometry(); wg.setAttribute('position', new THREE.BufferAttribute(wp, 3));
  MAT.weather = new THREE.PointsMaterial({ size: .06, color: 0xffffff, transparent: true, opacity: .8, depthWrite: false });
  heli = new THREE.Group(); const hb = new THREE.Mesh(kitGeo('heli'), MAT.vcM), rt = new THREE.Mesh(kitGeo('rotor'), MAT.vc), hl = new THREE.PointLight(0xfff0d0, 1.6, 26, 1.5);
  rt.position.set(0, 1.85, .4); hl.position.set(0, -1.2, 1.5); heli.add(hb, rt, hl); heli.userData.rotor = rt; heli.visible = false; scene.add(heli);
  for (let i = 0; i < 8; i++) { const p = new THREE.Points(wg, MAT.weather); p.frustumCulled = false; p.visible = false; scene.add(p); weatherPts.push(p); }
}

// ---------------------------------------------------------------- map generators
function Gen(w, h, fill) {
  const g = []; for (let r = 0; r < h; r++) g.push(new Array(w).fill(fill));
  const props = [], used = new Uint8Array(w * h);
  const G = { g, layers: [g], props, w, h, spawn: { c: 1, r: 1 }, bld: null,
    addLayer: () => { const a = []; for (let r = 0; r < h; r++) a.push(new Array(w).fill(' ')); G.layers.push(a); return a; },
    get: (c, r) => (c < 0 || r < 0 || c >= w || r >= h) ? '#' : g[r][c],
    set: (c, r, ch) => { if (c >= 0 && r >= 0 && c < w && r < h) g[r][c] = ch; },
    rect: (c0, r0, c1, r1, ch) => { for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) G.set(c, r, ch); },
    frame: (c0, r0, c1, r1, ch) => { for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) if (r === r0 || r === r1 || c === c0 || c === c1) G.set(c, r, ch); },
    open: (c, r) => OPEN[G.get(c, r)] === 1,
    free: (c, r) => OPEN[G.get(c, r)] === 1 && !used[r * w + c],
    ring: (c, r) => { for (let y = r - 1; y <= r + 1; y++) for (let x = c - 1; x <= c + 1; x++) if (!G.free(x, y)) return false; return true; },
    reserve: (c, r, rad) => { for (let y = r - rad; y <= r + rad; y++) for (let x = c - rad; x <= c + rad; x++) if (x >= 0 && y >= 0 && x < w && y < h) used[y * w + x] = 1; },
    add: (k, c, r, o) => { props.push(Object.assign({ k, c, r }, o || {})); if (k !== 'light') used[r * w + c] = 1; return G; },
    deco: o => { props.push(o); return G; },
    nearDoor: (c, r) => N4.some(d => isDoor(G.get(c + d[0], r + d[1]))),
    // furniture / junk pushed up against exactly one wall, never in a corridor or doorway
    clutter: (kinds, n, test) => { let t = n * 50; while (n > 0 && t-- > 0) { const c = 1 + lpick(w - 2), r = 1 + lpick(h - 2); if (!G.free(c, r) || !test(g[r][c]) || G.nearDoor(c, r)) continue;
      const ds = N4.filter(d => HARD[G.get(c + d[0], r + d[1])]); if (ds.length !== 1) continue; const d = ds[0]; if (!G.free(c - d[0], r - d[1])) continue;
      G.add(kinds[lpick(kinds.length)], c, r, { dx: d[0], dz: d[1] }); n--; } },
    // loose decoration with no collision
    scatter: (k, n, test, o) => { let t = n * 30; while (n > 0 && t-- > 0) { const c = lpick(w), r = lpick(h); if (!G.free(c, r) || !test(g[r][c])) continue;
      props.push(Object.assign({ k, x: wx(c) + lr(-1.3, 1.3), z: wx(r) + lr(-1.3, 1.3), c, r }, o || {})); n--; } }
    ,
    // free-standing junk, kept off the centre line of its tile so paths stay clear
    loose: (kinds, n, test) => { let t = n * 30; while (n > 0 && t-- > 0) { const c = 1 + lpick(w - 2), r = 1 + lpick(h - 2); if (!G.free(c, r) || !test(g[r][c]) || G.nearDoor(c, r)) continue;
      const a = lr(0, 6.28); props.push({ k: kinds[lpick(kinds.length)], x: wx(c) + Math.cos(a) * .95, z: wx(r) + Math.sin(a) * .95, c, r, loose: 1 }); used[r * w + c] = 1; n--; } },
    // well spread open spots for objectives and extra crates
    spots: n => { const cand = [], out = [], sp = G.spawn;
      for (let t = 0; t < 6000 && cand.length < 400; t++) { const c = 2 + lpick(w - 4), r = 2 + lpick(h - 4); if (!G.free(c, r)) continue; let ok = true; for (let y = -1; y <= 1; y++) for (let x = -1; x <= 1; x++) if (!G.open(c + x, r + y)) ok = false; if (ok) cand.push([c, r, LR() * 2]); }
      const sc = q => { let d = Math.hypot(q[0] - sp.c, q[1] - sp.r); for (const o of out) d = Math.min(d, Math.hypot(q[0] - o[0], q[1] - o[1])); return Math.min(d, 15) + q[2]; };
      for (let i = 0; i < n && cand.length; i++) { let b = 0, bd = -1; cand.forEach((q, j) => { const d = sc(q); if (d > bd) { bd = d; b = j; } }); out.push(cand[b]); G.reserve(cand[b][0], cand[b][1], 1); cand.splice(b, 1); }
      return out; }
  };
  return G;
}
// three generators, four supply cases, one hold point, then any extra Mystery Crates
function objectives(G, crates, noZone) {
  const s = G.spots(7 + crates + (noZone ? 0 : 1) + 7); let i = 0;
  for (let k = 0; k < 3 && i < s.length; k++, i++) G.props.push({ k: 'gen', c: s[i][0], r: s[i][1], i: k, ry: lr(0, 6) });
  for (let k = 0; k < 4 && i < s.length; k++, i++) G.props.push({ k: 'sup', c: s[i][0], r: s[i][1], i: k });
  if (!noZone && i < s.length) { G.props.push({ k: 'zone', c: s[i][0], r: s[i][1] }); i++; }
  for (let k = 0; k < crates && i < s.length; k++, i++) G.add('crate', s[i][0], s[i][1]);
  // then gun racks, a workbench and extra ammo stations, and free ammo boxes lying about
  const pool = Object.keys(WCOST), big = G.g.length * G.g[0].length;
  for (let k = 0; k < 4 && i < s.length; k++, i++) G.add('rack', s[i][0], s[i][1], { w: pool.splice(lpick(pool.length), 1)[0] });
  if (i < s.length) { G.add('wbench', s[i][0], s[i][1]); i++; }
  for (; i < s.length; i++) G.add('ammo', s[i][0], s[i][1]);
  G.loose(['abox'], Math.max(8, Math.min(26, Math.round(big / 230))), ch => OPEN[ch] === 1);
  for (const p of G.props) if (p.k === 'abox') p.ry = lr(0, 6.28);
  // set dressing: ceiling pipes, hanging chains, scattered papers, bones, candles, graves and stakes
  const ind = ch => ch === '.', outd = ch => ch === ',', any = ch => OPEN[ch] === 1, kk = big / 1000;
  G.scatter('cpipe', Math.round(10 * kk + 6), ind); G.scatter('chain', Math.round(6 * kk + 4), ind); G.scatter('papers', Math.round(14 * kk + 8), ind); G.scatter('bones', Math.round(12 * kk + 6), any);
  G.scatter('candle', Math.round(3 * kk + 3), any); G.scatter('grave', Math.round(8 * kk), outd); G.scatter('stake', Math.round(5 * kk + 1), outd);
}
const CARCOL = [0x6a1f1c, 0x26384e, 0x8a8c8a, 0x2c2e30, 0x7a6a44, 0x39503c, 0xa8a69c, 0x4a2c50];
function addCar(G, c, r, ry) { const burnt = LR() < .24; G.add('car', c, r, { ry, van: LR() < .22, col: burnt ? 0x1a1612 : CARCOL[lpick(CARCOL.length)], fire: burnt && LR() < .45, tilt: burnt ? lr(-.06, .06) : 0, sink: burnt }); }
// two-storey lookout: a small house with stairs inside, up to a walled roof you can shoot down from
function lookout(G, c0, r0, door, wall) {
  const c1 = c0 + 6, r1 = r0 + 5, A = r0 + 1, s = c0 + 2, L0 = G.layers[0]; while (G.layers.length < 2) G.addLayer(); const L1 = G.layers[1];
  for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) { const edge = r === r0 || r === r1 || c === c0 || c === c1; L0[r][c] = edge ? wall : '.'; L1[r][c] = edge ? 'p' : ','; }
  L0[A][s] = '1'; L0[A][s + 1] = '2'; L0[A + 1][s] = L0[A + 1][s + 1] = '#'; L1[A][s] = 'x'; L1[A][s + 1] = 'v'; L1[A + 1][s] = L1[A + 1][s + 1] = 'p';
  const d = door === 'w' ? [c0, r0 + 3] : door === 'e' ? [c1, r0 + 3] : [c0 + 4, r1]; L0[d[1]][d[0]] = '.';
  for (let r = r0 - 1; r <= r1 + 1; r++) for (let c = c0 - 1; c <= c1 + 1; c++) G.reserve(c, r, 0);
  G.props.push({ k: 'light', c: c0 + 4, r: r0 + 3, m: 1 }, { k: 'exit', x: wx(d[0]), z: wx(d[1]) }, { k: 'box', c: c0 + 1, r: r0 + 4, dx: -1, dz: 0 }, { k: 'shelf', c: c0 + 5, r: r0 + 2, dx: 1, dz: 0 },
    { k: 'abox', x: wx(c0 + 5), z: wx(r0 + 4) + .9, l: 1, ry: 1 }, { k: 'sandbag', c: c0 + 5, r: r0 + 2, l: 1, dx: 1, dz: 0 }, { k: 'stack', c: c0 + 1, r: r0 + 4, l: 1, dx: -1, dz: 0 });
}
// plain one-room cabin with a pitched roof
function cabin(G, c0, r0, door) {
  const c1 = c0 + 5, r1 = r0 + 4; G.frame(c0, r0, c1, r1, '#'); G.rect(c0 + 1, r0 + 1, c1 - 1, r1 - 1, '.');
  const d = door === 'w' ? [c0, r0 + 2] : door === 'e' ? [c1, r0 + 2] : [c0 + 2, r1]; G.set(d[0], d[1], '.');
  for (let r = r0 - 1; r <= r1 + 1; r++) for (let c = c0 - 1; c <= c1 + 1; c++) G.reserve(c, r, 0);
  G.props.push({ k: 'light', c: c0 + 3, r: r0 + 2, m: 1 }, { k: 'bed', c: c0 + 1, r: r0 + 1, dx: -1, dz: 0 }, { k: 'shelf', c: c1 - 1, r: r0 + 1, dx: 1, dz: 0 }, { k: 'desk', c: c0 + 3, r: r0 + 1, dx: 0, dz: -1 },
    { k: 'abox', x: wx(c1 - 1), z: wx(r1 - 1) + .8, ry: .6 }, { k: 'roof', x: (wx(c0) + wx(c1)) / 2, z: (wx(r0) + wx(r1)) / 2, sx: 6 * TILE + 1.2, sz: 5 * TILE + 1.2, h: 2.4 });
}
function genWard() {
  const A = [
    '############################', '#S...o#S...........#,,,,,,s#', '#.....#.....L......#,t,,,,,#', '#..L..a............b,,,,,,,#', '#.....#....##......#,,,M,,,#',
    '#.....#....##......#,,,,,,,#', '#o....#......P....o#,,,,,t,#', '#..A..#............#,,,,,,,#', '#.....#.....L.....S#s,,,,,,#', '###.#######c########,,t,,,,#',
    '#.....#o...........#,,,,,,,#', '#..L..#..S...L.....####d####', '#.....#....##......#.......#', '#.....e....##......f...L...#', '#.....#............#o......#',
    '#..S..#......L.....#..H....#', '#.....#............#.......#', '#....o#..S........o#.....S.#', '#..L..#............#...L...#', '#.....#............#.......#', '############################'];
  const G = Gen(28, A.length, '.');
  A.forEach((row, r) => { for (let c = 0; c < 28; c++) { const ch = row[c];
    G.g[r][c] = ch === '#' ? '#' : ',stM'.indexOf(ch) >= 0 ? ',' : isDoor(ch) ? ch : '.';
    if (ch === 'P') { G.spawn = { c, r }; G.reserve(c, r, 1); }
    if (ch === 'S' || ch === 's') G.add('zs', c, r); if (ch === 'L') G.add('light', c, r); if (ch === 'o') G.add('barrel', c, r, { box: 1 });
    if (ch === 't') G.add('dtree', c, r, { s: 1.1 }); if (ch === 'M') G.add('crate', c, r); if (ch === 'A') G.add('ammo', c, r); if (ch === 'H') G.add('stim', c, r); } });
  objectives(G, 1);
  G.clutter(['bed', 'bed', 'bed', 'locker', 'cabinet', 'desk', 'chair', 'shelf', 'bodybag'], 46, ch => ch === '.');
  G.clutter(['stack', 'box', 'pallet', 'box', 'vending', 'ladder', 'sandbag'], 22, ch => true);
  G.clutter(['bench', 'box', 'barrel', 'bags'], 6, ch => ch === ',');
  G.scatter('deb', 170, ch => ch === '.'); G.scatter('rubble', 10, ch => ch === '.'); G.scatter('bodybag', 8, ch => ch === '.'); G.scatter('deb', 40, ch => ch === ',');
  G.scatter('hang', 10, ch => ch === '.'); G.scatter('pool', 46, ch => true);
  return G;
}
function genWoods() {
  const n = 76, m = n - 1, G = Gen(n, n, ','), g = G.g;
  for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (c < 2 || r < 2 || c > m - 2 || r > m - 2) g[r][c] = 'T';
  for (let i = 0; i < 70; i++) { const k = 2 + lpick(n - 4), s = lpick(4); G.set(s === 0 ? 2 : s === 1 ? m - 2 : k, s === 2 ? 2 : s === 3 ? m - 2 : k, 'T'); }
  G.spawn = { c: 23, r: 29 }; G.reserve(23, 29, 2);
  // cabin
  G.frame(20, 18, 26, 23, '#'); G.rect(21, 19, 25, 22, '.'); G.set(23, 23, 'a'); G.reserve(23, 20, 5);
  G.add('ammo', 21, 19).add('light', 23, 20, { m: 1 }).add('bed', 25, 20, { dx: 1, dz: 0 }).add('desk', 23, 19, { dx: 0, dz: -1 }).add('shelf', 21, 21, { dx: -1, dz: 0 }).add('chair', 25, 22, { dx: 0, dz: 1 });
  G.deco({ k: 'roof', x: wx(23), z: (wx(18) + wx(23)) / 2, sx: 7 * TILE + 1.4, sz: 6 * TILE + 1.4, h: 2.8 });
  // shed
  G.frame(35, 8, 39, 12, '#'); G.rect(36, 9, 38, 11, '.'); G.set(35, 10, 'b'); G.reserve(37, 10, 4);
  G.add('stim', 38, 10).add('light', 37, 10, { m: 1 }).add('box', 37, 9, { dx: 0, dz: -1 });
  G.deco({ k: 'roof', x: wx(37), z: wx(10), sx: 5 * TILE + 1.2, sz: 5 * TILE + 1.2, h: 2.2 });
  // ranger station ruin (open walls) and a campsite
  G.frame(44, 26, 50, 31, '#'); G.rect(45, 27, 49, 30, '.'); for (const q of [[47, 26], [44, 28], [50, 29], [47, 31], [48, 31], [45, 26]]) G.set(q[0], q[1], '.'); G.reserve(47, 28, 5);
  G.add('light', 47, 28, { m: 1 }).add('desk', 49, 27, { dx: 1, dz: 0 }).add('locker', 45, 30, { dx: -1, dz: 0 }).add('zs', 48, 29);
  G.reserve(44, 46, 3);
  for (const q of [[42.5, 45, .4], [45.5, 44, 2.2], [44, 48, 4.2]]) G.deco({ k: 'tent', x: q[0] * TILE, z: q[1] * TILE, ry: q[2] });
  G.deco({ k: 'fire', x: wx(44) + 1.5, z: wx(46) + 1.5 }).deco({ k: 'lantern', x: wx(46), z: wx(47), ry: 1 });
  G.add('crate', 9, 35); G.reserve(9, 35, 2);
  G.deco({ k: 'lantern', x: wx(9) + 2.3, z: wx(35) - 2.3, ry: 2 }).deco({ k: 'lantern', x: wx(23) + 2.2, z: wx(24) - .6, ry: 3.6 }).deco({ k: 'lantern', x: wx(34) - .5, z: wx(10) + 2.2, ry: 5 }).deco({ k: 'lantern', x: wx(30), z: wx(30), ry: 1 }).deco({ k: 'lantern', x: wx(15), z: wx(15), ry: 4 }).deco({ k: 'lantern', x: wx(20), z: wx(48), ry: 2 }).deco({ k: 'lantern', x: wx(50), z: wx(14), ry: 3 });
  G.deco({ k: 'fire', x: wx(23) + 2.6, z: wx(29) - 2.6 });
  for (const q of [[5, 5], [23, 4], [40, 5], [4, 23], [41, 22], [5, 40], [23, 41], [40, 40], [13, 14], [33, 30], [12, 28], [32, 17], [16, 38], [36, 36], [54, 6], [54, 30], [54, 53], [30, 54], [8, 54], [50, 42], [28, 48], [52, 18]]) { G.set(q[0], q[1], ','); G.add('zs', q[0], q[1]); G.reserve(q[0], q[1], 1); }
  G.add('car', 14, 23, { ry: .6, col: 0x39503c, sink: true }); G.reserve(14, 23, 1); G.add('car', 31, 38, { ry: 2.3, van: true, col: 0x8a8c8a }); G.reserve(31, 38, 1); G.add('car', 40, 50, { ry: 1.1, col: 0x6a1f1c, sink: true }); G.reserve(40, 50, 1);
  // lookouts you can climb, more cabins further out, and more places for them to come from
  lookout(G, 28, 40, 's', '#'); lookout(G, 62, 10, 's', '#'); lookout(G, 10, 62, 'e', '#'); lookout(G, 60, 60, 'w', '#'); cabin(G, 64, 36, 's'); cabin(G, 36, 64, 'e');
  for (const q of [[66, 5], [70, 24], [66, 46], [70, 70], [48, 70], [24, 70], [5, 66], [58, 22], [20, 58], [44, 58]]) { G.set(q[0], q[1], ','); G.add('zs', q[0], q[1]); G.reserve(q[0], q[1], 1); }
  objectives(G, 3);
  G.loose(['box', 'stack', 'barrel', 'pallet', 'sandbag', 'box', 'stack'], 100, ch => ch === ',');
  for (let i = 0, k = 0; i < 900 && k < 60; i++) { const c = 4 + lpick(n - 8), r = 4 + lpick(n - 8); if (!G.ring(c, r)) continue; g[r][c] = 'R'; G.reserve(c, r, 1); k++; }
  for (let r = 2; r < n - 2; r++) for (let c = 2; c < n - 2; c++) { if (g[r][c] !== ',' || !G.free(c, r) || LR() > .3) continue; const a = lr(0, 6.28), d = lr(.75, 1.15);
    G.deco({ k: LR() < .78 ? 'pine' : 'dtree', x: wx(c) + Math.cos(a) * d, z: wx(r) + Math.sin(a) * d, s: lr(.8, 1.4), ry: lr(0, 6) }); }
  const snow = ch => ch === ','; G.scatter('log', 46, snow); G.scatter('stump', 60, snow); G.scatter('drift', 280, snow); G.scatter('deb', 150, snow); G.scatter('deb', 30, ch => ch === '.');
  G.scatter('pool', 40, ch => true); G.scatter('bodybag', 14, snow); G.scatter('hang', 3, ch => ch === '.');
  return G;
}
function genBack() {
  const n = 57, G = Gen(n, n, '.'), g = G.g; G.frame(0, 0, n - 1, n - 1, '#');
  for (let i = 1; i < n - 1; i++) { g[i][19] = g[i][38] = '#'; g[19][i] = g[38][i] = '#'; }
  const doors = [[28, 19, 'a'], [28, 38, 'b'], [19, 28, 'c'], [38, 28, 'd'], [19, 9, 'e'], [38, 9, 'e'], [19, 47, 'e'], [38, 47, 'e'], [9, 19, 'f'], [9, 38, 'f'], [47, 19, 'f'], [47, 38, 'f']];
  G.spawn = { c: 28, r: 28 };
  const prot = new Uint8Array(n * n), P = (c, r, rad) => { for (let y = r - rad; y <= r + rad; y++) for (let x = c - rad; x <= c + rad; x++) prot[y * n + x] = 1; };
  for (const d of doors) { g[d[1]][d[0]] = d[2]; P(d[0], d[1], 2); }
  P(28, 28, 1); P(28, 9, 1); P(28, 47, 1); P(47, 47, 1);
  const q = new Int32Array(n * n), seen = new Uint8Array(n * n);
  const walk = () => { seen.fill(0); let h = 0, t = 0; q[t++] = 28 * n + 28; seen[28 * n + 28] = 1;
    while (h < t) { const i = q[h++], c = i % n, r = (i / n) | 0; for (const d of N4) { const x = c + d[0], y = r + d[1], j = y * n + x; if (x < 0 || y < 0 || x >= n || y >= n || seen[j] || g[y][x] === '#') continue; seen[j] = 1; q[t++] = j; } }
    return t; };
  let total = 0; for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (g[r][c] !== '#') total++;
  for (let i = 0; i < 620; i++) { const c = 2 + 2 * lpick(27), r = 2 + 2 * lpick(27), hz = LR() < .5, len = 1 + lpick(4), cells = [];
    for (let k = 0; k < len; k++) { const x = c + (hz ? k : 0), y = r + (hz ? 0 : k); if (G.get(x, y) !== '.' || prot[y * n + x]) break; cells.push([x, y]); }
    if (!cells.length) continue; for (const [x, y] of cells) g[y][x] = '#';
    if (walk() !== total - cells.length) { for (const [x, y] of cells) g[y][x] = '.'; } else total -= cells.length; }
  G.reserve(28, 28, 1); G.add('ammo', 28, 9); G.add('stim', 28, 47); G.add('crate', 47, 47); G.reserve(28, 9, 1); G.reserve(28, 47, 1); G.reserve(47, 47, 1);
  objectives(G, 2);
  for (let r = 2; r < n - 1; r += 3) for (let c = 2; c < n - 1; c += 3) if (g[r][c] === '.') G.add('light', c, r, { m: LR() < .4 ? 2 : LR() < .75 ? 1 : 0 });
  for (let s = 0; s < 9; s++) for (let k = 0, t = 0; k < 3 && t < 400; t++) { const c = 2 + lpick(16) + (s % 3) * 19, r = 2 + lpick(16) + ((s / 3) | 0) * 19; if (!G.free(c, r) || Math.hypot(c - 28, r - 28) < 6) continue; G.add('zs', c, r); k++; }
  G.clutter(['chair', 'desk', 'cabinet', 'shelf', 'box', 'chair', 'locker', 'bags', 'stack', 'vending', 'pallet', 'ladder', 'box', 'stack'], 150, ch => ch === '.'); G.loose(['box', 'stack', 'barrel', 'pallet', 'chair'], 40, ch => ch === '.'); G.scatter('deb', 150, ch => ch === '.'); G.scatter('rubble', 14, ch => ch === '.');
  G.scatter('hang', 16, ch => ch === '.'); G.scatter('pool', 70, ch => true); G.scatter('bodybag', 12, ch => true);
  return G;
}
function genHighway() {
  const w = 21, h = 150, e = h - 2, near = 80, far = 40, gs = 59, G = Gen(w, h, '#'), g = G.g;
  for (let r = 0; r < e; r++) { g[r][0] = g[r][1] = 'R'; if (r < 2) { for (let c = 2; c <= 12; c++) g[r][c] = 'R'; continue; }
    g[r][2] = g[r][3] = g[r][11] = g[r][12] = ','; for (let c = 4; c <= 10; c++) g[r][c] = '='; if (r % 8 < 6) g[r][7] = 'J'; }
  for (let c = 2; c <= 12; c++) { g[far][c] = '#'; g[near][c] = '#'; }
  g[near][9] = g[near][10] = 'a'; g[far][5] = g[far][6] = 'b'; g[far - 1][7] = g[far + 1][7] = g[near - 1][7] = g[near + 1][7] = '=';
  G.deco({ k: 'slab', x: 19.5, y: WALL_H + .55, z: wx(far), sx: 39, sy: 1.1, sz: 10, col: 0x6a6c6e }).deco({ k: 'slab', x: 19.5, y: WALL_H + 1.5, z: wx(far) - 4.85, sx: 39, sy: .9, sz: .3, col: 0x5a5c5e }).deco({ k: 'slab', x: 19.5, y: WALL_H + 1.5, z: wx(far) + 4.85, sx: 39, sy: .9, sz: .3, col: 0x5a5c5e });
  // gas station
  G.rect(13, gs - 5, 15, gs + 5, ','); G.rect(17, gs - 2, 18, gs + 2, '.'); g[gs][16] = 'c';
  G.add('stim', 18, gs - 2).add('light', 17, gs, { m: 1 }).add('shelf', 18, gs + 2, { dx: 1, dz: 0 }).add('pump', 14, gs - 1).add('pump', 14, gs + 1);
  G.deco({ k: 'slab', x: wx(14), y: 3.6, z: wx(gs), sx: 8.4, sy: .4, sz: 15.5, col: 0x8a2a22 });
  for (const a of [[-3.6, -7], [3.6, -7], [-3.6, 7], [3.6, 7]]) G.deco({ k: 'slab', x: wx(14) + a[0], y: 1.7, z: wx(gs) + a[1], sx: .28, sy: 3.4, sz: .28, col: 0x9a9a94 });
  G.spawn = { c: 5, r: h - 6 }; G.reserve(5, h - 6, 2); for (const q of [[5, far], [6, far], [9, near], [10, near]]) G.reserve(q[0], q[1], 2);
  G.add('ammo', 12, h - 16); G.add('crate', 12, 10); G.reserve(12, 10, 1); G.reserve(12, h - 16, 1);
  for (const q of [[2, 84], [12, 86], [3, 116], [2, 100], [11, 95], [9, 83], [2, 108], [2, 44], [12, 44], [2, 70], [12, 74], [3, 60], [9, 43], [2, 52], [12, 66], [2, 4], [12, 4], [2, 20], [12, 24], [6, 3], [9, 14], [2, 34], [12, 36]]) G.add('zs', q[0], q[1]);
  const nr = {}; for (const r0 of [15, 95, 124]) { lookout(G, 13, r0, 'w', '#'); nr[r0 + 2] = nr[r0 + 3] = nr[r0 + 4] = 1; }   // roadside lookouts over the carriageway
  for (const q of [[2, 126], [12, 132], [2, 138], [12, 122]]) G.add('zs', q[0], q[1]);
  const carAt = new Uint8Array(w * h);
  for (const q of [[5, 100, Math.PI], [9, 68, 0], [5, 50, Math.PI], [9, 24, 0], [5, 12, Math.PI]]) { G.deco({ k: 'truck', c: q[0], r: q[1], ry: q[2], col: CARCOL[lpick(CARCOL.length)] }); G.reserve(q[0], q[1], 2); for (let y = -2; y <= 2; y++) carAt[(q[1] + y) * w + q[0]] = 1; }
  objectives(G, 2);
  for (let r = 3; r < e - 1; r++) for (let c = 4; c <= 10; c++) { if (g[r][c] !== '=' || !G.free(c, r) || LR() > .17) continue;
    let ok = true; for (let y = -1; y <= 1; y++) for (let x = -1; x <= 1; x++) if (carAt[(r + y) * w + c + x]) ok = false; if (!ok) continue;
    carAt[r * w + c] = 1; addCar(G, c, r, LR() < .2 ? lr(0, 6.28) : (c < 7 ? Math.PI : 0) + lr(-.35, .35)); }
  for (let r = 4; r < e - 1; r += 6) { const ea = (r / 6 | 0) % 2; if (ea && r >= gs - 6 && r <= gs + 6) continue; G.deco({ k: 'lamp', x: ea ? wx(12) + 1.0 : wx(2) - 1.0, z: wx(r), ry: ea ? -Math.PI / 2 : Math.PI / 2, lit: LR() < .45 }); }
  for (let r = 2; r < e; r++) { if (LR() < .85) G.deco({ k: 'rail', x: 6.4, z: wx(r), ry: 0 }); if (LR() < .85 && (r < gs - 5 || r > gs + 5) && !nr[r]) G.deco({ k: 'rail', x: 38.6, z: wx(r), ry: Math.PI });
    if (r % 2 === 0 && r !== far && r !== near) for (const x of [15, 18, 27, 30]) G.deco({ k: 'dash', x, z: wx(r) }); }
  for (const x of [12.2, 20.8, 24.2, 32.8]) G.deco({ k: 'slab', x, y: .012, z: h * 1.5, sx: .14, sy: .02, sz: h * 3 - 14, col: 0x8a8778 });
  for (const r of [96, 64, 28, 108, 16, 128, 142]) G.deco({ k: 'gantry', x: 22.5, z: wx(r) + 1.4 });
  const dirt = ch => ch === ','; G.clutter(['barrel', 'box', 'tyres', 'dumpster', 'tyres', 'bags', 'stack', 'sandbag', 'pallet', 'stack'], 70, dirt); G.loose(['box', 'stack', 'barrel', 'pallet', 'sandbag', 'tyres', 'box'], 70, ch => ch === ',' || ch === '=');
  G.scatter('dtree', 34, dirt, { s: 1 }); G.scatter('sign', 14, dirt); G.scatter('deb', 360, ch => ch !== '#'); G.scatter('rubble', 36, ch => ch !== '#'); G.scatter('cone', 24, ch => ch === '='); G.scatter('bodybag', 10, ch => ch === '=');
  G.scatter('pool', 70, ch => true); G.scatter('hang', 2, ch => ch === '.');
  return G;
}
function genCity() {
  const NB = 7, n = NB * 12 + 2, m = n - 1, G = Gen(n, n, '='), g = G.g, bld = G.bld = new Uint8Array(n * n);
  G.frame(0, 0, m, m, 'B'); for (let i = 0; i < n; i++) bld[i] = bld[m * n + i] = bld[i * n] = bld[i * n + m] = 6;
  const building = (c0, r0, c1, r1, fl, ruin, lock, side) => {
    G.frame(c0, r0, c1, r1, 'B'); G.rect(c0 + 1, r0 + 1, c1 - 1, r1 - 1, '.'); for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) bld[r * n + c] = fl;
    const cm = (c0 + c1) >> 1, rm = (r0 + r1) >> 1, mid = s => s === 0 ? [cm, r0] : s === 1 ? [c1, rm] : s === 2 ? [cm, r1] : [c0, rm];
    if (lock) { const q = mid(side); g[q[1]][q[0]] = lock; return; }
    const sides = [lpick(2) * 2, 1 + lpick(2) * 2]; if (LR() < .5) sides.push((sides[0] + 2) % 4);
    for (const s of sides) { const q = mid(s), tall = r1 - r0 >= 4, off = -lpick(2); if (s % 2 === 0) g[q[1]][q[0] + off] = '.'; else g[q[1] + (tall ? off : 0)][q[0]] = '.'; }
    if (ruin) for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) { const er = r === r0 || r === r1, ec = c === c0 || c === c1; if (er !== ec && LR() < .2) { g[r][c] = '.'; G.deco({ k: 'rubble', x: wx(c) + lr(-.8, .8), z: wx(r) + lr(-.8, .8) }); } }
    if (c1 - c0 >= 6 && r1 - r0 >= 6) { if (LR() < .5) { const gap = r0 + 1 + lpick(r1 - r0 - 1); for (let r = r0 + 1; r < r1; r++) if (r !== gap) g[r][cm + 1] = '#'; } else { const gap = c0 + 1 + lpick(c1 - c0 - 1); for (let c = c0 + 1; c < c1; c++) if (c !== gap) g[rm + 1][c] = '#'; } }
    if (g[r0 + 1][c0 + 1] === '.') G.add('light', c0 + 1, r0 + 1, { m: LR() < .5 ? 2 : 1 }); if (g[r1 - 1][c1 - 1] === '.') G.add('light', c1 - 1, r1 - 1, { m: LR() < .6 ? 2 : 1 });
    if (LR() < .4 && G.free(c1 - 1, r0 + 1)) G.add('zs', c1 - 1, r0 + 1);
  };
  // the tower: a full block, F real floors joined by a switchback staircase, extraction pad on the roof
  const towers = [];
  const tower = (c0, r0, F, main) => {
    const c1 = c0 + 8, r1 = r0 + 8, s = c0 + 2, A = r0 + 1, B = r0 + 2, C = r0 + 3;
    while (G.layers.length <= F) G.addLayer();
    for (let l = 0; l <= F; l++) { const L = G.layers[l], roof = l === F, even = l % 2 === 0, P = (k, c, r, o) => G.props.push(Object.assign({ k, c, r, l }, o || {}));
      for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) { const edge = r === r0 || r === r1 || c === c0 || c === c1; L[r][c] = roof ? (edge ? 'p' : ',') : edge ? (l ? 'W' : 'B') : '.'; }
      if (!roof) { L[B][s] = L[B][s + 1] = L[C + 1][s] = L[C + 1][s + 1] = '#'; if (even) { L[A][s] = '1'; L[A][s + 1] = '2'; } else { L[C][s + 1] = '3'; L[C][s] = '4'; } L[r0 + 5][c0 + 5] = '#'; if (l % 3 === 1) L[r0 + 6][c0 + 2] = '#'; if (l % 3 === 2) L[r0 + 2][c0 + 6] = '#'; }
      else { L[B][s] = L[B][s + 1] = 'p'; }
      if (l > 0) { if (even) { L[C][s + 1] = 'x'; L[C][s] = 'v'; } else { L[A][s] = 'x'; L[A][s + 1] = 'v'; } } else L[C][s] = L[C][s + 1] = '#';
      if (roof) { if (main) P('evac', c0 + 5, r0 + 5); else { P('sandbag', c0 + 3, r0 + 7, { dx: 0, dz: 1 }); P('stack', c0 + 7, r0 + 5, { dx: 1, dz: 0 }); } P('ac', c0 + 7, r0 + 2); P('ac', c0 + 2, r0 + 6); P('ac', c0 + 7, r0 + 6, { ry: 1.57 }); P('zs', c0 + 1, r0 + 7); P('zs', c0 + 7, r0 + 4); continue; }
      P('light', c0 + 4, r0 + 2, { m: 0 }); P('light', c0 + 6, r0 + 3, { m: LR() < .5 ? 1 : 2 }); P('light', c0 + 3, r0 + 6, { m: 1 }); P('light', c0 + 6, r0 + 6, { m: LR() < .4 ? 0 : 2 });
      P('zs', c0 + 7, r0 + 7); if (l) P('zs', c0 + 7, r0 + 1);
      const fur = ['desk', 'shelf', 'locker', 'cabinet', 'chair', 'box', 'bed'];
      for (let r = r0 + 2; r <= r0 + 6; r++) if (LR() < .55 && !(l === 0 && r === r0 + 5)) P(fur[lpick(7)], c0 + 7, r, { dx: 1, dz: 0 });
      for (let c = c0 + 3; c <= c0 + 6; c++) if (LR() < .5 && !(l === 0 && c === c0 + 4) && L[r0 + 6][c] === '.') P(fur[lpick(7)], c, r0 + 7, { dx: 0, dz: 1 });
      for (let i = 0; i < 10; i++) G.props.push({ k: i < 8 ? 'deb' : 'rubble', x: wx(c0 + 5) + lr(-5, 8), z: wx(r0 + 5) + lr(-2, 8), l });
    }
    const L0 = G.layers[0]; L0[r0][c0 + 6] = '.'; L0[r1][c0 + 4] = '.'; L0[r0 + 5][c1] = '.';
    for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) bld[r * n + c] = 1;
    G.reserve(c0 + 2, r0 + 2, 2); G.reserve(c0 + 6, r0 + 6, 2); G.reserve(c0 + 6, r0 + 2, 1); G.reserve(c0 + 2, r0 + 6, 1);
    if (main) G.deco({ k: 'lamp', x: wx(c0 + 6) + 1.6, z: wx(r0) - 2.2, ry: Math.PI, lit: true });
    for (const q of [[c0 + 6, r0], [c0 + 4, r1], [c1, r0 + 5]]) G.deco({ k: 'exit', x: wx(q[0]), z: wx(q[1]), main });   // lit lintel over every way in to a climbable building
    towers.push({ c0, r0, F, main });
  };
  for (let i = 0; i < NB; i++) for (let j = 0; j < NB; j++) G.add('zs', 2 + 12 * i, 2 + 12 * j);
  for (let j = 0; j < NB; j++) for (let i = 0; i < NB; i++) { const c0 = 4 + i * 12, r0 = 4 + j * 12, c1 = c0 + 8, r1 = r0 + 8; G.rect(c0, r0, c1, r1, ',');
    if (i === 2 && j === 3) { tower(c0, r0, 5, true); continue; }
    for (const a of [[c0, r0, -1, -1], [c1, r0, 1, -1], [c0, r1, -1, 1], [c1, r1, 1, 1]]) { const lit = LR() < .45 || (i === 2 && j === 2);
      if (LR() < .6) G.deco({ k: 'lamp', x: wx(a[0]) + a[2] * 1.0, z: wx(a[1]) + a[3] * 1.0, ry: Math.atan2(a[2], 0), lit }); else if (LR() < .5) G.deco({ k: 'tlight', x: wx(a[0]) + a[2] * 1.05, z: wx(a[1]) + a[3] * 1.05, ry: a[3] > 0 ? 0 : Math.PI });
      else if (LR() < .6) G.deco({ k: 'pole', x: wx(a[0]) + a[2] * 1.1, z: wx(a[1]) + a[3] * 1.1, ry: lr(0, 3) }); }
    if (i === 2 && j === 2) { G.spawn = { c: c0 + 4, r: r0 + 4 }; G.reserve(c0 + 4, r0 + 4, 2); G.deco({ k: 'fire', x: wx(c0 + 2) + 1.5, z: wx(r0 + 2) + 1.5, barrel: 1 }).deco({ k: 'fire', x: wx(c1 - 2) - 1.5, z: wx(r1 - 2) - 1.5, barrel: 1 }); continue; }
    if (i === 2 && j === 1) { building(c0 + 1, r0 + 1, c1 - 1, r1 - 1, 3, false, 'a', 2); G.add('ammo', c0 + 4, r0 + 4).add('light', c0 + 4, r0 + 3, { m: 0 }).add('locker', c0 + 2, r0 + 3, { dx: -1, dz: 0 }).add('shelf', c1 - 2, r0 + 3, { dx: 1, dz: 0 }); continue; }
    if (i === 1 && j === 2) { building(c0 + 1, r0 + 1, c1 - 1, r1 - 1, 4, false, 'b', 1); G.add('stim', c0 + 4, r0 + 4).add('light', c0 + 3, r0 + 4, { m: 1 }).add('bed', c0 + 2, r0 + 3, { dx: -1, dz: 0 }).add('cabinet', c0 + 4, r0 + 2, { dx: 0, dz: -1 }); continue; }
    if (i === 3 && j === 2) { G.add('crate', c0 + 4, r0 + 4); G.reserve(c0 + 4, r0 + 4, 1); G.deco({ k: 'lantern', x: wx(c0 + 4) + 2.4, z: wx(r0 + 4) - 2.4, ry: 2 }); continue; }
    const t = LR();
    if (t < .56) { if (LR() < .45) tower(c0, r0, 2 + lpick(3), false); else building(c0 + 1, r0 + 1, c1 - 1, r1 - 1, 2 + lpick(5), LR() < .35); }
    else if (t < .72) { building(c0 + 1, r0 + 1, c1 - 1, r0 + 3, 2 + lpick(3), false); building(c0 + 1, r0 + 5, c1 - 1, r1 - 1, 2 + lpick(3), LR() < .4); }
    else if (t < .86) { G.rect(c0, r0, c1, r1, '='); for (let r = r0 + 1; r < r1; r += 2) for (let c = c0 + 1; c < c1; c += 2) if (LR() < .55) addCar(G, c, r, lr(-.15, .15) + (LR() < .5 ? 0 : Math.PI)); }
    else for (let r = r0 + 1; r < r1; r++) for (let c = c0 + 1; c < c1; c++) if (LR() < .18) G.deco({ k: 'dtree', x: wx(c) + lr(.7, 1.1), z: wx(r) + lr(-1.1, -.7), s: lr(.8, 1.2) });
  }
  // the hold point sits on one rooftop and a Mystery Crate on another
  const side = towers.filter(t => !t.main).sort((a, b) => Math.hypot(a.c0 - 28, a.r0 - 28) - Math.hypot(b.c0 - 28, b.r0 - 28));
  if (side[0]) G.props.push({ k: 'zone', c: side[0].c0 + 5, r: side[0].r0 + 5, l: side[0].F });
  if (side[1]) G.props.push({ k: 'crate', c: side[1].c0 + 5, r: side[1].r0 + 5, l: side[1].F });
  objectives(G, 3, !!side[0]);
  const carAt = new Uint8Array(n * n), street = v => (v - 1) % 12 < 3;
  for (let r = 1; r < m; r++) for (let c = 1; c < m; c++) { if (g[r][c] !== '=' || !G.free(c, r)) continue; const vs = street(c), hs = street(r); if (!vs && !hs) continue;
    if (!(vs && hs) && ((vs && (c - 1) % 12 === 1 && r % 2) || (hs && (r - 1) % 12 === 1 && c % 2))) G.deco({ k: 'dash', x: wx(c), z: wx(r), ry: vs ? 0 : Math.PI / 2 });
    if (LR() > .075) continue; let ok = true; for (let y = -1; y <= 1; y++) for (let x = -1; x <= 1; x++) if (carAt[(r + y) * n + c + x] || !G.open(c + x, r + y)) ok = false; if (!ok) continue;
    carAt[r * n + c] = 1; addCar(G, c, r, LR() < .25 ? lr(0, 6.28) : (vs ? 0 : Math.PI / 2) + lr(-.3, .3) + (LR() < .5 ? Math.PI : 0)); }
  G.clutter(['dumpster', 'box', 'barrel', 'tyres', 'bench', 'hydrant', 'dumpster', 'bags', 'mailbox', 'bags'], 130, ch => ch === ',');
  G.clutter(['desk', 'shelf', 'locker', 'cabinet', 'chair', 'bed', 'desk', 'box', 'stack', 'vending', 'pallet', 'ladder'], 200, ch => ch === '.');
  G.clutter(['stack', 'box', 'pallet', 'sandbag', 'ladder', 'vending', 'stack', 'box'], 90, ch => ch === ',');
  G.loose(['box', 'stack', 'barrel', 'pallet', 'sandbag', 'tyres', 'box', 'stack'], 170, ch => ch === ',' || ch === '=');
  G.scatter('deb', 800, ch => true); G.scatter('rubble', 90, ch => true); G.scatter('cone', 20, ch => ch === '='); G.scatter('sign', 30, ch => ch === ','); G.scatter('bodybag', 16, ch => ch !== '.');
  G.scatter('hang', 30, ch => ch === '.'); G.scatter('pool', 160, ch => true);
  return G;
}
const MAPS = {
  ward: { name: 'Hollow Ward', desc: 'Abandoned hospital', seed: 101, gen: genWard,
    doors: { a: { cost: 750, name: 'the West Ward' }, b: { cost: 1250, name: 'the Courtyard' }, c: { cost: 1000, name: 'the South Hall' }, d: { cost: 1250, name: 'the Morgue' }, e: { cost: 1000, name: 'the Service Corridor' }, f: { cost: 1000, name: 'the Morgue Passage' } },
    theme: { fog: 0x020305, dens: .068, hemi: [0x31405c, 0x0a0a08, .11], sun: null, wall: ['wallA', 'wallB'], wk: 'in', floor: 'floor', ceil: 'ceil', ground: 'ground', road: 'asphalt', deb: 0x6a6a62, rock: 0x55585a, light: 0xd9e2b0 } },
  woods: { name: 'Winter Woods', desc: 'Bigger forest: cabins, camp, lookouts to climb', seed: 4242, gen: genWoods,
    doors: { a: { cost: 750, name: 'the Cabin' }, b: { cost: 1250, name: 'the Shed' } },
    theme: { fog: 0x080d15, dens: .05, hemi: [0x7088b4, 0x1a1e28, .26], sun: [0x8fa8d8, .16], wall: ['plank', 'plank'], wk: 'plank', floor: 'woodfloor', ceil: 'woodfloor', ground: 'snow', road: 'snow', deb: 0xaab4c4, rock: 0x70767e, light: 0xffc880, weather: 'snow' } },
  back: { name: 'The Back Rooms', desc: 'Endless yellow maze, nine sections', seed: 777, gen: genBack,
    doors: { a: { cost: 750, name: 'the North Rooms' }, b: { cost: 750, name: 'the South Rooms' }, c: { cost: 1000, name: 'the West Rooms' }, d: { cost: 1000, name: 'the East Rooms' }, e: { cost: 1500, name: 'the Corner Rooms (all four ways in)' }, f: { cost: 1500, name: 'the Corner Rooms (all four ways in)' } },
    theme: { fog: 0x090804, dens: .055, hemi: [0x8a8040, 0x2a2610, .16], sun: null, wall: ['paper', 'paper'], wk: 'in', floor: 'carpet', ceil: 'ctile', ground: 'carpet', road: 'carpet', deb: 0x6a6238, rock: 0x55585a, light: 0xfff0a8, panel: true } },
  highway: { name: 'Dead Highway', desc: 'Longer ruined road, wrecks, roadside lookouts', seed: 9090, gen: genHighway,
    doors: { a: { cost: 750, name: 'the Checkpoint' }, b: { cost: 1250, name: 'the Overpass' }, c: { cost: 1000, name: 'the Gas Station' } },
    theme: { fog: 0x0c0705, dens: .034, hemi: [0x8a6a5a, 0x1a1410, .3], sun: [0xd88050, .2], wall: ['concrete', 'concrete'], wk: 'rib', floor: 'floor', ceil: 'ceil', ground: 'dirt', road: 'asphalt', deb: 0x4a4a48, rock: 0x4a4440, light: 0xffb060, weather: 'ember' } },
  city: { name: 'Broken City', desc: 'Huge city. Climb the tower and extract from the roof', seed: 31337, gen: genCity,
    doors: { a: { cost: 750, name: 'the Armory' }, b: { cost: 1000, name: 'the Clinic' } },
    theme: { fog: 0x06080c, dens: .032, hemi: [0x6a7ca4, 0x16161a, .26], sun: [0x8aa0d0, .16], wall: ['wallA', 'wallB'], wk: 'in', bwall: 'brick', facade: 'facade', floor: 'floor', ceil: 'ceil', ground: 'sidewalk', road: 'asphalt', deb: 0x5a5a58, rock: 0x55585a, light: 0xffc890, weather: 'ember' } }
};

// ---------------------------------------------------------------- level build
function tileMesh(l, list, y, up, mat, uvS) {
  const pos = [], nor = [], uv = [], col = [], hard = (c, r) => { const ch = tileL(l, c, r); return ch === '#' || ch === 'B' || ch === 'W'; };
  for (const [c, r, sh] of list) {
    const x0 = c * TILE, x1 = x0 + TILE, z0 = r * TILE, z1 = z0 + TILE;
    const ao = (cc, rr) => { const v = sh * (.8 + ((cc * 7 + rr * 13 + (cc * rr) % 3) % 5) * .05); return (hard(cc - 1, rr - 1) || hard(cc, rr - 1) || hard(cc - 1, rr) || hard(cc, rr)) ? v * .42 : v; };   // dark where floor meets wall
    const a = ao(c, r), b = ao(c + 1, r), d = ao(c, r + 1), e = ao(c + 1, r + 1);
    const q = up ? [[x0, z0, a], [x0, z1, d], [x1, z1, e], [x0, z0, a], [x1, z1, e], [x1, z0, b]] : [[x0, z0, a], [x1, z1, e], [x0, z1, d], [x0, z0, a], [x1, z0, b], [x1, z1, e]];
    for (const v of q) { pos.push(v[0], y, v[1]); nor.push(0, up ? 1 : -1, 0); uv.push(v[0] / uvS, v[1] / uvS); col.push(v[2], v[2], v[2]); }
  }
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); g.setAttribute('normal', new THREE.Float32BufferAttribute(nor, 3));
  g.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); g.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
  const m = new THREE.Mesh(g, mat); m.receiveShadow = true; return m;
}
// The level's walls and props are split into square patches so that only the ones near you and on screen are drawn.
const NORAY = { pine: 1, pineL: 1, dtree: 1, deb: 1, papers: 1, bones: 1, pool: 1, drift: 1, chain: 1, candle: 1, rubble: 1 };   // foliage and litter: bullets pass through, which keeps shots cheap
const chunks = [], CHK = 36, _fr = new THREE.Frustum(), _pm = new THREE.Matrix4();
function instChunks(list, posOf, make) {
  const by = {}; for (const p of list) { const q = posOf(p), k = q[2] ? 'big' : Math.floor(q[0] / CHK) + ',' + Math.floor(q[1] / CHK); (by[k] = by[k] || []).push(p); }
  for (const k in by) { const a = k.split(','), m = make(by[k]); m.frustumCulled = false;
    if (m.userData.noRay) m.raycast = () => {}; else if (k !== 'big') { const cen = new THREE.Vector3((+a[0] + .5) * CHK, 8, (+a[1] + .5) * CHK), R = CHK * .71 + 15;   // bullets only test the patches their path actually crosses
      m.raycast = function (rc, hits) { if (rc.ray.distanceSqToPoint(cen) > R * R || rc.ray.origin.distanceTo(cen) > rc.far + R) return; THREE.InstancedMesh.prototype.raycast.call(this, rc, hits); }; }
    chunks.push({ m, s: k === 'big' ? new THREE.Sphere(new THREE.Vector3(camera.position.x, 0, camera.position.z), 1e5) : new THREE.Sphere(new THREE.Vector3((+a[0] + .5) * CHK, 8, (+a[1] + .5) * CHK), CHK * .71 + 15) }); }
}
function cullChunks() {
  camera.updateMatrixWorld(); camera.matrixWorldInverse.copy(camera.matrixWorld).invert(); _pm.multiplyMatrices(camera.projectionMatrix, camera.matrixWorldInverse); _fr.setFromProjectionMatrix(_pm);
  const far = 2.7 / scene.fog.density, cx = camera.position.x, cz = camera.position.z;   // past this the fog has swallowed everything anyway
  for (const c of chunks) { const dx = c.s.center.x - cx, dz = c.s.center.z - cz, lim = far + c.s.radius; c.m.visible = dx * dx + dz * dz < lim * lim && _fr.intersectsSphere(c.s); }
}
function loadMap(id) {
  const def = MAPS[id] || MAPS.ward; MAPID = MAPS[id] ? id : 'ward';
  if (levelGroup) { scene.remove(levelGroup); levelGroup.traverse(o => { if (o.geometry && !o.geometry.userData.keep) o.geometry.dispose(); }); }
  levelGroup = new THREE.Group(); scene.add(levelGroup); propGroup = new THREE.Group(); doorGroup = new THREE.Group(); levelGroup.add(propGroup, doorGroup);
  zSpawns.length = 0; interactables.length = 0; aboxes.length = 0; colliders.length = 0; lightSpots.length = 0; crateObj = null; crateShow = null; EVAC = null; PY = 0; PL = 0; OBJ = { gens: [], sups: [], zone: null, list: [] };
  for (const k in doorOpen) delete doorOpen[k]; for (const k in doorMesh) delete doorMesh[k];
  for (const p of pool) { p.spot = null; p.l.intensity = 0; }
  instQ = {}; wallQ = {}; glowQ = []; LR = seeded(def.seed);
  const d = def.gen(), T = THEME = def.theme;
  LAYERS = d.layers; MAP = LAYERS[0]; NL = LAYERS.length; H = MAP.length; W = MAP[0].length; DOORS = def.doors; bldF = d.bld;
  flow = new Int16Array(W * H * NL); navBlock = new Uint8Array(W * H * NL); flowT = 0;
  SPAWN = { x: wx(d.spawn.c), z: wx(d.spawn.r) }; shootables = [doorGroup, propGroup, zGroup];
  for (let l = 0; l < NL; l++) {
    const L = LAYERS[l], y0 = l * FH, fl = {}, ceil = [], pushF = (name, c, r) => { (fl[name] = fl[name] || []).push([c, r, 1]); };
    for (let r = 0; r < H; r++) for (let c = 0; c < W; c++) {
      const ch = L[r][c], x = wx(c), z = wx(r); if (ch === ' ') continue;
      if (ch === '#') pushW(T.wall[(c * 7 + r * 13) % 5 === 0 ? 1 : 0], T.wk, x, y0 + WALL_H / 2, z);
      else if (ch === 'B') pushW(T.bwall, 'brick', x, y0 + WALL_H / 2, z);
      else if (ch === 'W') pushW(T.facade, 'fwall', x, y0 + WALL_H / 2, z);
      else if (ch === 'p') put('cube', x, y0 + .55, z, 0, TILE, 1.1, TILE, 0x4c4e50);
      else if (ch === 'x' || ch === 'v') { if (l < NL - 1 && LAYERS[l + 1][r][c] !== ' ') ceil.push([c, r, 1]); }
      else {
        const up = l < NL - 1 ? LAYERS[l + 1][r][c] : ' ';
        const indoor = ch === '.' || STAIR[ch] || (isDoor(ch) && N4.some(q => tileL(l, c + q[0], r + q[1]) === '.'));
        if (indoor) { pushF(T.floor, c, r); if (up !== 'x' && up !== 'v') ceil.push([c, r, 1]); } else pushF(ch === '=' || ch === 'J' ? T.road : T.ground, c, r);
        if (isDoor(ch)) addDoor(ch, c, r);
        if (ch === '1') put('stair', x + TILE / 2, y0, z, 0); if (ch === '3') put('stair', x - TILE / 2, y0, z, Math.PI);
        if (ch === 'T') for (let i = 0, k = 2 + lpick(2); i < k; i++) { const s = lr(1.1, 1.7); put('pineL', x + lr(-1.2, 1.2), 0, z + lr(-1.2, 1.2), lr(0, 6), s, s * lr(.9, 1.3), s); }
        if (ch === 'R') put('rock', x + lr(-.3, .3), -.1, z + lr(-.3, .3), lr(0, 6), lr(1.75, 2.15), lr(1.7, 3.4), lr(1.75, 2.15), T.rock);
        if (ch === 'J') put('barrier', x, 0, z, 0);
      }
      const f = bldF && !l ? bldF[r * W + c] : 0;
      if (f > 1 && N4.some(q => { const cc = c + q[0], rr = r + q[1]; return cc >= 0 && rr >= 0 && cc < W && rr < H && !bldF[rr * W + cc]; })) for (let k = 1; k < f; k++) pushW(T.facade, 'facade', x, k * WALL_H + WALL_H / 2, z);
    }
    for (const name in fl) { const m = tileMesh(l, fl[name], y0, true, texMat(name), UVS[name] || 6); levelGroup.add(m); shootables.push(m); }
    if (ceil.length) { const m = tileMesh(l, ceil, y0 + WALL_H - .03, false, texMat(T.ceil), 3); levelGroup.add(m); shootables.push(m); }
  }
  d.props.forEach(placeProp);
  if (OBJ.gens.length) OBJ.list.push({ t: 'gen', n: OBJ.gens.length, title: 'Start the generators' });
  if (OBJ.sups.length) OBJ.list.push({ t: 'sup', n: OBJ.sups.length, title: 'Recover the supply cases' });
  if (OBJ.zone) OBJ.list.push({ t: 'hold', n: 40, title: 'Hold the signal point' });
  if (EVAC) OBJ.list.push({ t: 'evac', n: 1, title: 'Climb the tower and extract from the roof' });
  const o = new THREE.Object3D(), tc = new THREE.Color();
  chunks.length = 0;
  for (const key in wallQ) { const kk = key.split('|'), geo = wallGeo(kk[1]), mat = texMat(kk[0]);
    instChunks(wallQ[key], p => [p[0], p[2]], list => { const m = new THREE.InstancedMesh(geo, mat, list.length); list.forEach((p, i) => { o.position.set(p[0], p[1], p[2]); o.updateMatrix(); m.setMatrixAt(i, o.matrix); });
      m.receiveShadow = true; m.castShadow = kk[1] !== 'facade'; levelGroup.add(m); if (kk[1] !== 'facade') shootables.push(m); return m; }); }
  for (const kind in instQ) instChunks(instQ[kind], p => { const e = p[0].elements; return [e[12], e[14], Math.max(Math.hypot(e[0], e[1], e[2]), Math.hypot(e[4], e[5], e[6]), Math.hypot(e[8], e[9], e[10])) > 9]; }, list => { const m = new THREE.InstancedMesh(kitGeo(kind), METAL[kind] ? MAT.vcM : MAT.vc, list.length);
    list.forEach((p, i) => { m.setMatrixAt(i, p[0]); m.setColorAt(i, tc.set(p[1] === undefined ? 0xffffff : p[1]).convertSRGBToLinear()); });
    m.receiveShadow = true; m.castShadow = !NOSHADOW[kind]; m.userData.noRay = !!NORAY[kind]; propGroup.add(m); return m; });
  glowMesh = new THREE.InstancedMesh(KGEO.glowBox, MAT.glow, Math.max(1, glowQ.length)); glowMesh.frustumCulled = false;
  if (!glowQ.length) { o.position.set(0, -99, 0); o.updateMatrix(); glowMesh.setMatrixAt(0, o.matrix); glowMesh.setColorAt(0, tc.set(0)); }
  glowQ.forEach((p, i) => { glowMesh.setMatrixAt(i, p[0]); glowMesh.setColorAt(i, tc.set(p[1]).convertSRGBToLinear()); }); levelGroup.add(glowMesh);
  // atmosphere
  scene.background.set(T.fog); scene.fog.color.set(T.fog); scene.fog.density = T.dens * FOGK;
  hemi.color.set(T.hemi[0]); hemi.groundColor.set(T.hemi[1]); hemi.intensity = Math.max(T.hemi[2] * VIS, .2);
  sun.intensity = T.sun ? T.sun[1] : 0; if (T.sun) sun.color.set(T.sun[0]);
  skyGroup.userData.stars.material.opacity = T.weather === 'snow' ? .25 : .7; skyGroup.userData.moon.material.color.set(T.weather === 'ember' ? 0xb08a70 : 0xbfc8d8);
  MAT.weather.color.set(T.weather === 'ember' ? 0xff8a30 : 0xe8eef8); MAT.weather.size = T.weather === 'ember' ? .03 : .05;
  if (flashlight) flashlight.distance = T.dens < .04 ? 44 : 34;
  if (heli) heli.visible = false;
}
const HUGS = { bed: [.98, .5, 1], locker: [1.2, .5, 1], cabinet: [1.18, .45, 0], shelf: [1.22, .5, 1], desk: [1.05, .5, 1], chair: [.9, .28, 0], dumpster: [.95, .6, 1], bench: [1.1, .35, 1], box: [.95, .5, 0], tyres: [1.05, .42, 0], hydrant: [.9, .2, 0], barrel: [1.0, .42, 0], bags: [1.0, .42, 0], mailbox: [1.08, .3, 0], bodybag: [.85, .15, 0], stack: [.95, .5, 1], pallet: [.9, .5, 0], sandbag: [1.1, .4, 1], vending: [1.13, .45, 0], ladder: [1.25, .15, 0] };
const BARCOL = [0x6a4a34, 0x2c3c50, 0x5a2420, 0x3a4630, 0x55504a];
function placeProp(p) {
  PL = p.l || 0; PY = PL * FH; const c0 = colliders.length, i0 = interactables.length;
  placeProp0(p);
  for (let i = c0; i < colliders.length; i++) colliders[i].l = PL; for (let i = i0; i < interactables.length; i++) interactables[i].l = PL;
  PL = 0; PY = 0;
}
function placeProp0(p) {
  const k = p.k, T = THEME; let x = p.x !== undefined ? p.x : wx(p.c), z = p.z !== undefined ? p.z : wx(p.r);
  const nb = () => { navBlock[nidx(PL, p.c, p.r)] = 1; };
  if (k === 'zs') zSpawns.push({ c: p.c, r: p.r, x, z, l: PL });
  else if (k === 'light') { const dead = p.m === 2, pn = T.panel;
    put('cube', x, WALL_H - .03, z, 0, pn ? 1.32 : 1.3, .08, pn ? 1.32 : .42, 0x1c1c1c);
    const gi = glow(x, WALL_H - .085, z, pn ? 1.16 : 1.12, .04, pn ? 1.16 : .26, dead ? 0x191914 : T.light);
    if (!dead) spot(x, WALL_H - .45, z, T.light, lr(.65, 1) * (pn ? 1.7 : .95), pn ? 13 : 11, p.m === undefined ? (LR() < .55 ? 1 : 0) : p.m, gi); }
  else if (k === 'crate') { addCrate(x, z); nb(); }
  else if (k === 'abox') addAmmoBox(x, z, p.ry || 0);
  else if (k === 'rack') { addRack(x, z, p.w); nb(); }
  else if (k === 'wbench') { addBench(x, z); nb(); }
  else if (k === 'ammo' || k === 'stim') { addStation(k, x, z); nb(); }
  else if (k === 'car') { const ry = p.ry || 0, s = Math.sin(ry), c = Math.cos(ry);
    put(p.van ? 'van' : 'car', x, p.sink ? -.14 : 0, z, ry, 1, 1, 1, p.col, 0, p.tilt || 0); nb();
    for (const o of [-1.45, 0, 1.45]) colliders.push({ x: x + s * o, z: z + c * o, r: p.van ? 1.05 : .95 });
    if (p.fire) { const gi = glow(x + s * 1.3, 1.0, z + c * 1.3, .8, .35, .8, 0xff7a20, ry); spot(x + s * 1.3, 1.7, z + c * 1.3, 0xff7a28, 1.8, 14, 2, gi); } }
  else if (k === 'pine' || k === 'dtree') { const s = p.s || 1; put(k, x, 0, z, p.ry === undefined ? lr(0, 6) : p.ry, s, s * lr(.9, 1.2), s); colliders.push({ x, z, r: .3 * s }); }
  else if (HUGS[k] && p.loose) { put(k, x, 0, z, lr(0, 6), 1, 1, 1, k === 'barrel' ? BARCOL[lpick(5)] : undefined); colliders.push({ x, z, r: Math.min(.5, HUGS[k][1]) }); }
  else if (HUGS[k] && p.dx !== undefined) { const h = HUGS[k], tx = -p.dz, tz = p.dx; x += p.dx * h[0]; z += p.dz * h[0];
    put(k, x, 0, z, Math.atan2(-p.dx, -p.dz), 1, 1, 1, k === 'barrel' ? BARCOL[lpick(5)] : undefined);
    if (h[2]) colliders.push({ x: x + tx * .5, z: z + tz * .5, r: h[1] }, { x: x - tx * .5, z: z - tz * .5, r: h[1] }); else colliders.push({ x, z, r: h[1] }); }
  else if (k === 'barrel') { put('barrel', x, 0, z, lr(0, 6), 1, 1, 1, BARCOL[lpick(5)]); colliders.push({ x, z, r: .45 }); if (p.box) { put('box', x + .85, 0, z + .25, lr(0, 6), .8, .8, .8); colliders.push({ x: x + .85, z: z + .25, r: .45 }); } }
  else if (k === 'lamp') { const ry = p.ry || 0; put('lamp', x, 0, z, ry); colliders.push({ x, z, r: .22 });
    const lx = x + Math.sin(ry) * 1.5, lz = z + Math.cos(ry) * 1.5, gi = glow(lx, 5.96, lz, .26, .05, .62, p.lit ? T.light : 0x15140f, ry); if (p.lit) spot(lx, 5.5, lz, T.light, 1.5, 18, LR() < .3 ? 1 : 0, gi); }
  else if (k === 'lantern') { const ry = p.ry || 0; put('lantern', x, 0, z, ry); colliders.push({ x, z, r: .15 });
    const lx = x + Math.sin(ry) * .45, lz = z + Math.cos(ry) * .45; spot(lx, 1.9, lz, 0xffb060, 1.25, 11, 2, glow(lx, 1.88, lz, .12, .24, .12, 0xffc070)); }
  else if (k === 'fire') { if (p.barrel) { put('barrel', x, 0, z, 0, 1, 1, 1, 0x2a2420); spot(x, 1.5, z, 0xff7a28, 1.7, 13, 2, glow(x, 1.1, z, .56, .1, .56, 0xff8a28)); colliders.push({ x, z, r: .45 }); }
    else { put('logs', x, 0, z, lr(0, 6)); spot(x, .9, z, 0xff7a28, 1.9, 15, 2, glow(x, .22, z, .42, .36, .42, 0xff8a28, .6)); colliders.push({ x, z, r: .55 }); } }
  else if (k === 'roof') { put('roof', x, WALL_H, z, 0, p.sx, p.h, p.sz, 0x3a3028); put('cube', x, WALL_H + .02, z, 0, p.sx, .12, p.sz, 0x2a221c); put('roof', x, WALL_H + .1, z, 0, p.sx + .3, p.h * .92, p.sz + .3, 0xaab4c4); }
  else if (k === 'slab') put('cube', x, p.y, z, p.ry || 0, p.sx, p.sy, p.sz, p.col);
  else if (k === 'dash') put('cube', x, .012, z, p.ry || 0, .16, .02, 1.7, 0x8a8778);
  else if (k === 'rail') put('rail', x, 0, z, p.ry || 0);
  else if (k === 'pump') { put('pump', x, 0, z, 0); colliders.push({ x, z, r: .55 }); }
  else if (k === 'cone') put('cone', x, 0, z, lr(0, 6), 1, 1, 1, undefined, LR() < .4 ? 1.45 : 0);
  else if (k === 'log') put('log', x, 0, z, lr(0, 6), lr(.8, 1.3), lr(.8, 1.2), lr(.8, 1.2));
  else if (k === 'stump') put('stump', x, 0, z, lr(0, 6), lr(.8, 1.4), lr(.6, 1.4), lr(.8, 1.4));
  else if (k === 'drift') { const sy = lr(.5, 1.1); put('drift', x, -sy * .62, z, lr(0, 6), lr(1.4, 3.2), sy, lr(1.4, 2.8)); }
  else if (k === 'rubble') put('rubble', x, 0, z, lr(0, 6), lr(.8, 1.6), lr(.7, 1.3), lr(.8, 1.6), T.deb === 0xaab4c4 ? 0xffffff : undefined);
  else if (k === 'truck') { const ry = p.ry || 0, s = Math.sin(ry), c = Math.cos(ry); put('truck', x, 0, z, ry, 1, 1, 1, p.col);
    for (let o = -4.4; o <= 4.5; o += 1.45) colliders.push({ x: x + s * o, z: z + c * o, r: 1.3 }); for (let y = -1; y <= 1; y++) navBlock[nidx(0, p.c, p.r + y)] = 1; }
  else if (k === 'tent') { put('tent', x, 0, z, p.ry || 0); colliders.push({ x, z, r: 1.15 }); }
  else if (k === 'tlight' || k === 'pole') { put(k, x, 0, z, p.ry || 0); colliders.push({ x, z, r: .22 }); }
  else if (k === 'gantry') put('gantry', x, 0, z, 0);
  else if (k === 'ac') { put('acunit', x, 0, z, p.ry || 0); colliders.push({ x, z, r: .85 }); }
  else if (k === 'evac') { EVAC = { x, y: PY, z, l: PL }; put('cube', x, .02, z, 0, 7.6, .04, 7.6, 0x26282a);
    for (const q of [[-1.2, 0, .4, 3], [1.2, 0, .4, 3], [0, 0, 2.4, .4]]) glow(x + q[0], .06, z + q[1], q[2], .03, q[3], 0xd8cfa0);
    for (const q of [[-3.6, -3.6], [3.6, -3.6], [-3.6, 3.6], [3.6, 3.6]]) { put('cube', x + q[0], .2, z + q[1], 0, .16, .4, .16, 0x202224); spot(x + q[0], .6, z + q[1], 0xff3020, .9, 7, 1, glow(x + q[0], .45, z + q[1], .14, .14, .14, 0xff3020)); }
    interactables.push({ type: 'evac', x, z, cost: 0, range: 3.6 }); }
  else if (k === 'deb') for (let i = 0, n = 1 + lpick(3); i < n; i++) { const s = lr(.06, .26); put('deb', x + lr(-.5, .5), -s * .1, z + lr(-.5, .5), lr(0, 6), s, s * lr(.4, 1), s * lr(.7, 1.5), T.deb, lr(0, .5), lr(0, .5)); }
  else if (k === 'exit') { const col = p.main ? 0x30ff70 : 0xffb030; spot(x, 2.9, z, col, .7, 9, 0, glow(x, 3.42, z, 2.3, .2, 2.3, col)); }
  else if (k === 'gen') { put('gen', x, 0, z, p.ry || 0); nb(); colliders.push({ x, z, r: .85 });
    const lamp = new THREE.Mesh(KGEO.glowBox, new THREE.MeshBasicMaterial({ color: 0xff2010 })); lamp.scale.set(.2, .2, .2); lamp.position.set(x, PY + 1.72, z); levelGroup.add(lamp);
    OBJ.gens[p.i] = { x, z, l: PL, y: PY, lamp }; interactables.push({ type: 'gen', id: p.i, x, z, cost: 0, range: 2.7 }); }
  else if (k === 'sup') { const m = new THREE.Mesh(kitGeo('case'), MAT.vc), b = new THREE.Mesh(KGEO.glowBox, MAT.beacon); b.scale.set(.1, 10, .1); b.position.y = 5.4; m.add(b);
    m.position.set(x, PY, z); m.rotation.y = lr(0, 6); m.visible = false; levelGroup.add(m); OBJ.sups[p.i] = { x, z, l: PL, y: PY, m }; }
  else if (k === 'zone') { const rg = new THREE.RingGeometry(4.5, 5, 48); rg.rotateX(-Math.PI / 2); const m = new THREE.Mesh(rg, MAT.beacon), b = new THREE.Mesh(KGEO.glowBox, MAT.beacon); b.scale.set(.25, 14, .25); b.position.y = 7; m.add(b);
    m.position.set(x, PY + .05, z); m.visible = false; levelGroup.add(m); OBJ.zone = { x, z, l: PL, y: PY, m }; }
  else if (k === 'pool') put('pool', x, .012, z, lr(0, 6), lr(.4, 1.5), 1, lr(.4, 1.3));
  else if (k === 'cpipe') put('cpipe', wx(p.c), WALL_H - .28, wx(p.r), lpick(2) * Math.PI / 2);
  else if (k === 'chain') put('chain', x, WALL_H - .05, z, lr(0, 6));
  else if (k === 'candle') { put('candle', x, 0, z, lr(0, 6)); spot(x, .5, z, 0xff9a40, .5, 5, 2, glow(x, .22, z, .03, .05, .03, 0xffb060)); }
  else if (KITS[k]) put(k, x, 0, z, lr(0, 6));
}
function addDoor(ch, c, r) {
  const m = new THREE.Mesh(kitGeo('barricade'), MAT.vc); m.position.set(wx(c), 0, wx(r));
  if (!(solid(c - 1, r) && solid(c + 1, r))) m.rotation.y = Math.PI / 2;
  m.castShadow = m.receiveShadow = true; doorGroup.add(m); (doorMesh[ch] = doorMesh[ch] || []).push(m);
  interactables.push({ type: 'door', id: ch, x: wx(c), z: wx(r), cost: DOORS[ch].cost, range: 3.2 });
}
function openDoor(ch) {
  if (doorOpen[ch]) return; doorOpen[ch] = true;
  for (const m of doorMesh[ch] || []) { doorGroup.remove(m); if (G.started) { _v.set(m.position.x, 1.6, m.position.z); burst(_v, 30, [.25, .18, .1], 3); sNoise(300, .5, distVol(m.position.x, m.position.z, 40)); } }
  flowT = 0;
}
function signMat(key, draw, col) {
  return MAT[key] || (MAT[key] = new THREE.MeshBasicMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#060606'; g.fillRect(0, 0, s, s); g.fillStyle = col; g.strokeStyle = col; draw(g, s); }) }));
}
function addCrate(x, z) {
  const g = new THREE.Group(); g.position.set(x, PY, z);
  const base = new THREE.Mesh(new THREE.BoxGeometry(1.6, .62, .85), MAT.wood); base.position.y = .31; g.add(base);
  for (const sx of [-.6, 0, .6]) { const band = new THREE.Mesh(new THREE.BoxGeometry(.1, .66, .89), MAT.metal); band.position.set(sx, .32, 0); g.add(band); }
  for (const sx of [-.82, .82]) { const hd = new THREE.Mesh(new THREE.BoxGeometry(.04, .08, .3), MAT.metal); hd.position.set(sx, .42, 0); g.add(hd); }
  const lidP = new THREE.Group(); lidP.position.set(0, .62, -.425); g.add(lidP);
  const lid = new THREE.Mesh(new THREE.BoxGeometry(1.64, .12, .89), MAT.wood); lid.position.set(0, .06, .425); lidP.add(lid);
  for (const sx of [-.6, 0, .6]) { const band = new THREE.Mesh(new THREE.BoxGeometry(.1, .14, .91), MAT.metal); band.position.set(sx, .06, .425); lidP.add(band); }
  const sm = signMat('signQ', (c, s) => { c.font = '900 100px Georgia'; c.textAlign = 'center'; c.fillText('?', s / 2, s * .78); }, '#58b8ff');
  for (const sz of [-1, 1]) for (const sx of [-.3, .3]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.36, .36), sm); q.position.set(sx, .31, sz * .431); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
  g.traverse(o => { if (o.isMesh) { o.castShadow = true; o.receiveShadow = true; } });
  propGroup.add(g); colliders.push({ x: x - .4, z, r: .55 }, { x: x + .4, z, r: .55 });
  if (!MAT.cbeam) MAT.cbeam = new THREE.MeshBasicMaterial({ color: 0x4aa8ff, transparent: true, opacity: .3, depthWrite: false });
  if (!crateShow) { crateShow = { show: new THREE.Group(), models: {} }; levelGroup.add(crateShow.show);
    for (const id in WEAPONS) { if (id === 'pistol') continue; const m = buildGun(id, false); m.scale.setScalar(1.6); m.rotation.y = Math.PI / 2; m.visible = false; crateShow.show.add(m); crateShow.models[id] = m; } }
  const beam = new THREE.Mesh(KGEO.glowBox, MAT.cbeam); beam.scale.set(.07, 7, .07); beam.position.y = 4.2; g.add(beam);   // thin light so crates can be found from a distance
  crateObj = { g, lidP, glow: spot(x, 1.2, z, 0x4aa8ff, .8, 8, 0), show: crateShow.show, models: crateShow.models, x, z, y: PY };
  interactables.push({ type: 'crate', x, z, cost: COST.crate, range: 2.4, ref: crateObj });
}
// small free ammo box: each player can take it once, and they are refilled every second wave
function addAmmoBox(x, z, ry) {
  const g = new THREE.Group(); g.position.set(x, PY, z); g.rotation.y = ry; g.scale.setScalar(1.35);
  const mk = (w, h, l, mat, px, py, pz) => { const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, l), mat); m.position.set(px, py, pz); m.castShadow = true; m.receiveShadow = true; g.add(m); return m; };
  mk(.52, .26, .3, MAT.olive, 0, .13, 0); mk(.54, .05, .32, MAT.metal, 0, .285, 0); mk(.16, .03, .04, MAT.metal, 0, .325, 0); for (const sx of [-.27, .27]) mk(.02, .08, .14, MAT.metal, sx, .17, 0);
  const sm = signMat('signA', (c, s) => { for (let i = 0; i < 4; i++) { c.fillRect(22 + i * 24, 44, 14, 60); c.beginPath(); c.arc(29 + i * 24, 44, 7, Math.PI, 0); c.fill(); } }, '#ffd040');
  for (const sz of [-1, 1]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.2, .2), sm); q.position.set(0, .13, sz * .152); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
  if (!MAT.abeam) MAT.abeam = new THREE.MeshBasicMaterial({ color: 0xffc040, transparent: true, opacity: .55 });
  const lamp = new THREE.Mesh(KGEO.glowBox, MAT.abeam); lamp.scale.set(.05, .05, .05); lamp.position.set(.18, .33, 0); g.add(lamp);
  propGroup.add(g); const ref = { g, taken: false }; aboxes.push(ref);
  interactables.push({ type: 'abox', x, z, cost: 0, range: 1.9, ref });
}
// wall rack selling one particular gun
function addRack(x, z, wid) {
  const g = new THREE.Group(); g.position.set(x, PY, z);
  const mk = (w, h, l, mat, px, py, pz) => { const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, l), mat); m.position.set(px, py, pz); m.castShadow = true; m.receiveShadow = true; g.add(m); return m; };
  mk(1.7, 1.0, .08, MAT.wood, 0, 1.25, 0); mk(1.78, .07, .14, MAT.metal, 0, 1.78, 0); mk(1.78, .07, .14, MAT.metal, 0, .72, 0);
  for (const sx of [-.78, .78]) { mk(.09, 1.8, .09, MAT.metal, sx, .9, 0); mk(.14, .05, .6, MAT.metal, sx, .03, 0); }
  for (const sz of [-1, 1]) { const m = buildGun(wid, false); m.scale.setScalar(2.1); m.rotation.y = sz * Math.PI / 2; m.position.set(-sz * .12, 1.3, sz * .1); g.add(m);
    for (const sx of [-.3, .3]) mk(.03, .03, .1, MAT.metal, sx, 1.2, sz * .08); }
  propGroup.add(g); spot(x, 2.1, z, 0xffb050, .6, 6, 0);
  interactables.push({ type: 'wbuy', x, z, cost: WCOST[wid], id: wid, range: 2.4 }); colliders.push({ x: x - .5, z, r: .45 }, { x: x + .5, z, r: .45 });
}
// workbench: upgrades the gun you are holding
function addBench(x, z) {
  const g = new THREE.Group(); g.position.set(x, PY, z);
  const mk = (w, h, l, mat, px, py, pz) => { const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, l), mat); m.position.set(px, py, pz); m.castShadow = true; m.receiveShadow = true; g.add(m); return m; };
  mk(1.7, .08, .8, MAT.metal, 0, .9, 0); mk(1.6, .1, .7, MAT.wood, 0, .82, 0); for (const sx of [-.75, .75]) for (const sz of [-.32, .32]) mk(.08, .8, .08, MAT.metal, sx, .4, sz); mk(1.5, .05, .6, MAT.wood, 0, .25, 0);
  mk(.22, .16, .16, MAT.metal, -.55, 1.02, .1); mk(.06, .2, .2, MAT.metal, -.4, 1.04, .1); mk(.4, .22, .24, MAT.olive, .45, 1.05, -.1); mk(.42, .03, .26, MAT.metal, .45, 1.17, -.1); mk(.5, .04, .08, MAT.metal, 0, .96, .22);
  mk(1.7, .7, .05, MAT.metal, 0, 1.6, -.38); for (const sx of [-.8, .8]) mk(.06, 1.1, .06, MAT.metal, sx, 1.45, -.38);
  const sm = signMat('signU', (c, s) => { c.beginPath(); c.moveTo(s / 2, s * .1); c.lineTo(s * .86, s * .5); c.lineTo(s * .62, s * .5); c.lineTo(s * .62, s * .9); c.lineTo(s * .38, s * .9); c.lineTo(s * .38, s * .5); c.lineTo(s * .14, s * .5); c.fill(); }, '#40e0a0');
  const q = new THREE.Mesh(new THREE.PlaneGeometry(.5, .5), sm); q.position.set(0, 1.6, -.35); g.add(q); const q2 = q.clone(); q2.position.z = -.41; q2.rotation.y = Math.PI; g.add(q2);
  propGroup.add(g); spot(x, 1.9, z + .3, 0x40e0a0, .7, 7, 0);
  interactables.push({ type: 'up', x, z, cost: UP_COST, range: 2.4 }); colliders.push({ x: x - .5, z, r: .5 }, { x: x + .5, z, r: .5 });
}
function addStation(type, x, z) {
  const g = new THREE.Group(); g.position.set(x, 0, z);
  const mk = (w, h, l, mat, px, py, pz) => { const m = new THREE.Mesh(new THREE.BoxGeometry(w, h, l), mat); m.position.set(px, py, pz); g.add(m); return m; };
  if (type === 'ammo') {
    mk(1.2, .8, .75, MAT.olive, 0, .4, 0); mk(1.26, .08, .8, MAT.metal, 0, .82, 0); mk(1.26, .06, .8, MAT.metal, 0, .03, 0); mk(.5, .3, .4, MAT.olive, .25, 1.0, 0); mk(.3, .06, .06, MAT.metal, .25, 1.17, 0);
    for (const sx of [-.64, .64]) mk(.04, .1, .3, MAT.metal, sx, .55, 0);
    const sm = signMat('signA', (c, s) => { for (let i = 0; i < 4; i++) { c.fillRect(22 + i * 24, 44, 14, 60); c.beginPath(); c.arc(29 + i * 24, 44, 7, Math.PI, 0); c.fill(); } }, '#ffd040');
    for (const sz of [-1, 1]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.5, .5), sm); q.position.set(0, .42, sz * .381); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
    spot(x, 1.4, z, 0xffc040, .5, 6, 0);
    interactables.push({ type: 'ammo', x, z, cost: COST.ammo, range: 2.3 }); colliders.push({ x, z, r: .7 });
  } else {
    mk(.95, 1.9, .6, MAT.white, 0, .95, 0); mk(1.0, .08, .64, MAT.metal, 0, 1.92, 0); mk(1.0, .1, .64, MAT.metal, 0, .05, 0); mk(.6, .5, .03, MAT.metal, 0, .55, .31); mk(.3, .12, .08, MAT.metal, 0, .3, .33);
    const sm = signMat('signH', (c, s) => { c.fillRect(s * .38, s * .12, s * .24, s * .76); c.fillRect(s * .12, s * .38, s * .76, s * .24); }, '#ff3030');
    for (const sz of [-1, 1]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.55, .55), sm); q.position.set(0, 1.3, sz * .306); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
    spot(x, 1.5, z + .8, 0xff3838, .55, 6, 0);
    interactables.push({ type: 'stim', x, z, cost: COST.stim, range: 2.3 }); colliders.push({ x, z, r: .65 });
  }
  g.traverse(o => { if (o.isMesh) { o.castShadow = true; o.receiveShadow = true; } });
  propGroup.add(g);
}
const VIS = 1.36, FOGK = .82;   // a little more ambient light and thinner fog than the raw theme values
const _lc = new THREE.Color(), _white = new THREE.Color(0xc8d4ff);
function updateLights(dt) {
  const cx = camera.position.x, cz = camera.position.z, T = THEME; let dirty = false;
  if (G.started && !G.over) {
    blackNext -= dt; if (blackNext <= 0 && lightSpots.length > 3) { blackNext = rnd(45, 100); blackT = rnd(3.5, 7); sPowerDown(); setTimeout(() => sWhisper(1), 900); if (Math.random() < .5) setTimeout(() => sScream(.25, rnd(-1, 1)), 2200); }
    flashNext -= dt; if (flashNext <= 0) { flashNext = rnd(14, 42); if (T.sun) { flashT = .6; setTimeout(sThunder, rnd(300, 1800)); } }
    L.ambT -= dt; if (L.ambT <= 0) { L.ambT = rnd(6, 16); ambientEvent(); }
  }
  // blackout: every light dies for a few seconds, then stutters back
  let bo = 1; if (blackT > 0) { blackT -= dt; bo = blackT < .5 && Math.random() < .5 ? .7 : 0; }
  let fl = 0; if (flashT > 0) { flashT -= dt; fl = flashT > .45 || (flashT < .3 && flashT > .16) ? 1 : 0; }
  sun.intensity = (T.sun ? T.sun[1] : 0) + fl * 2.4; hemi.intensity = Math.max(T.hemi[2] * VIS, .2) + fl * 1.3; _lc.set(T.fog); if (fl) _lc.lerp(_white, .2); scene.background.copy(_lc); scene.fog.color.copy(_lc);
  for (const s of lightSpots) {
    if (s.mode === 1) { if (Math.random() < dt * 7) s.v = Math.random() < .42 ? rnd(0, .2) : rnd(.6, 1); }
    else if (s.mode === 2) s.v = .78 + Math.sin(G.time * 13 + s.ph) * .12 + Math.sin(G.time * 31 + s.ph * 2) * .1;
    else s.v = .93 + Math.sin(G.time * 9 + s.ph) * .04;
    const tv = s.v * (s.mode === 2 ? 1 : bo); if (s.gi >= 0 && Math.abs((s.pg === undefined ? 1 : s.pg) - tv) > .02) { s.pg = tv; glowMesh.setColorAt(s.gi, _lc.copy(s.gc).multiplyScalar(.05 + tv * .95)); dirty = true; } }
  if (dirty && glowMesh.instanceColor) glowMesh.instanceColor.needsUpdate = true;
  lightT -= dt;
  if (lightT <= 0) { lightT = .2;   // only the nearest few lights are real light sources; the rest are just glowing fixtures
    for (const s of lightSpots) s.d = Math.hypot(s.x - cx, s.z - cz) + Math.abs(s.y - camera.position.y) * (NL > 1 ? 2 : 0);
    const near = lightSpots.filter(s => s.d < 36).sort((a, b) => a.d - b.d).slice(0, pool.length);
    for (const p of pool) if (p.spot && near.indexOf(p.spot) < 0) { p.spot.pl = -1; p.spot = null; }
    for (const s of near) if (s.pl < 0) { const i = pool.findIndex(p => !p.spot); if (i < 0) break; pool[i].spot = s; s.pl = i; s.a = 0; } }
  for (const p of pool) { const s = p.spot; if (!s) { p.l.intensity = 0; continue; }
    s.a = Math.min(1, s.a + dt * 3); const d = Math.hypot(s.x - cx, s.z - cz);
    p.l.position.set(s.x, s.y, s.z); p.l.color.copy(s.col); p.l.distance = s.range; p.l.intensity = s.base * s.v * s.a * (s.mode === 2 ? 1 : bo) * Math.max(0, Math.min(1, (36 - d) / 6)); }
  // sky + weather follow the camera
  skyGroup.position.copy(camera.position);
  const wt = THEME.weather, wch = tileL((me && me.l) || 0, Math.floor(cx / TILE), Math.floor(cz / TILE)), out = wt && (wch === ',' || wch === '=' || wch === 'J' || !G.started), S = 24;
  const off = wt === 'snow' ? (G.time * 1.7) % 12 : 12 - (G.time * .8) % 12, bx = Math.floor(cx / S) * S, bz = Math.floor(cz / S) * S;
  const wy = Math.floor(camera.position.y / 12) * 12;
  weatherPts.forEach((p, i) => { p.visible = !!out; if (!out) return; p.position.set(bx + (i & 1) * S + Math.sin(G.time * .3) * .6, wy - off + ((i >> 2) & 1) * 12, bz + ((i >> 1) & 1) * S); });
  const on = EVAC && G.evacT > 0 && G.evacT < 45; heli.visible = !!on;
  if (on) { const k = Math.max(0, G.evacT - 8), h = EVAC.y + 6 + k * 2.2; heli.position.set(EVAC.x + Math.sin(G.time * .7) * .5, h, EVAC.z + k * 3); heli.rotation.y = Math.PI + Math.sin(G.time * .5) * .08; heli.rotation.x = k > 0 ? .12 : 0;
    heli.userData.rotor.rotation.y += dt * 28; if (Math.random() < dt * 10) sNoise(95, .1, Math.max(.05, .55 - k * .012)); }
}

// ---------------------------------------------------------------- collision
function blocked(e, x, z, rad) {
  const f = (a, b) => solidFor(e, Math.floor(a / TILE), Math.floor(b / TILE));
  return f(x - rad, z - rad) || f(x + rad, z - rad) || f(x - rad, z + rad) || f(x + rad, z + rad);
}
function moveCollide(e, nx, nz, rad) {
  let pc = Math.floor(e.x / TILE), pr = Math.floor(e.z / TILE); const tr = NL > 1;
  if (!blocked(e, nx, e.z, rad)) { e.x = nx; if (tr) { relevel(e, pc, pr); pc = Math.floor(e.x / TILE); } }
  if (!blocked(e, e.x, nz, rad)) { e.z = nz; if (tr) { relevel(e, pc, pr); pr = Math.floor(e.z / TILE); } }
  const l = e.l || 0;
  for (const c of colliders) { if ((c.l || 0) !== l) continue; const dx = e.x - c.x, dz = e.z - c.z, d = Math.hypot(dx, dz), m = rad + c.r;
    if (d < m && d > 1e-4) { const px = c.x + dx / d * m, pz = c.z + dz / d * m; if (!blocked(e, px, pz, rad)) { e.x = px; e.z = pz; if (tr) { relevel(e, pc, pr); pc = Math.floor(e.x / TILE); pr = Math.floor(e.z / TILE); } } } }
}

// ---------------------------------------------------------------- humanoids
const GEO = {};
// merge several primitive shapes into one smooth mesh (keeps draw calls low)
function merged(parts) {
  const pos = [], nor = [], uv = [];
  for (const [g0, m, fix] of parts) {
    const g = g0.index ? g0.toNonIndexed() : g0.clone(); if (m) g.applyMatrix4(m);
    const p = g.attributes.position.array, n = g.attributes.normal.array, u = g.attributes.uv.array;
    for (let i = 0; i < p.length; i++) { pos.push(p[i]); nor.push(n[i]); }
    for (let i = 0; i < u.length; i += 2) uv.push(fix ? fix[0] : u[i], fix ? fix[1] : u[i + 1]);
  }
  const o = new THREE.BufferGeometry();
  o.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); o.setAttribute('normal', new THREE.Float32BufferAttribute(nor, 3)); o.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2));
  return o;
}
function tearBlob(g, x, y, r, skin) {
  g.fillStyle = 'rgba(8,6,5,.9)'; g.beginPath(); for (let i = 0; i < 9; i++) { const a = i / 9 * 6.283, rr = r * rnd(.6, 1.25); g.lineTo(x + Math.cos(a) * rr, y + Math.sin(a) * rr * 1.3); } g.fill();
  g.fillStyle = skin; g.beginPath(); for (let i = 0; i < 9; i++) { const a = i / 9 * 6.283, rr = r * rnd(.45, .95); g.lineTo(x + Math.cos(a) * rr, y + Math.sin(a) * rr * 1.3); } g.fill();
  const gr = g.createRadialGradient(x, y, 0, x, y, r * .8); gr.addColorStop(0, 'rgba(55,4,3,.95)'); gr.addColorStop(1, 'rgba(55,4,3,0)'); g.fillStyle = gr; g.fillRect(x - r, y - r, r * 2, r * 2);
}
function veins(g, s, n, col) {
  g.strokeStyle = col; g.lineWidth = 1;
  for (let i = 0; i < n; i++) { let x = Math.random() * s, y = Math.random() * s; g.beginPath(); g.moveTo(x, y); for (let k = 0; k < 10; k++) { x += rnd(-9, 9); y += rnd(-9, 9); g.lineTo(x, y); } g.stroke(); }
}
function gash(g, x, y, r) {
  g.fillStyle = 'rgba(70,6,4,.9)'; g.beginPath(); g.ellipse(x, y, r, r * rnd(.3, .55), rnd(0, 3), 0, 7); g.fill();
  g.fillStyle = 'rgba(16,2,2,.95)'; g.beginPath(); g.ellipse(x, y, r * .6, r * .16, rnd(0, 3), 0, 7); g.fill();
}
function initGeo() {
  const cyl = (a, b, l, n) => new THREE.CylinderGeometry(a, b, l, n || 10), sph = (r, w, h) => new THREE.SphereGeometry(r, w || 12, h || 10);
  GEO.thigh = merged([[sph(.088), M(0, 0, 0)], [cyl(.086, .064, .46), M(0, -.23, 0)]]);
  GEO.shin = merged([[sph(.066), M(0, 0, 0)], [cyl(.062, .044, .42), M(0, -.21, 0)]]);
  GEO.foot = merged([[sph(.05), M(0, -.41, 0)], [new THREE.BoxGeometry(.095, .065, .2), M(0, -.435, .06)], [sph(.05), M(0, -.44, .16, 0, 0, 0, .95, .6, 1.2)]]);
  const prof = [[0, -.05], [.13, -.04], [.155, .05], [.15, .15], [.125, .27], [.15, .4], [.168, .5], [.155, .57], [.1, .62], [.052, .66], [.046, .74], [0, .74]].map(p => new THREE.Vector2(p[0], p[1]));
  GEO.torso = new THREE.LatheGeometry(prof, 18); GEO.torso.scale(1.2, 1, .72); GEO.torso.rotateY(Math.PI);
  GEO.upper = merged([[sph(.068), M(0, 0, 0)], [cyl(.056, .044, .32), M(0, -.16, 0)]]);
  GEO.fore = merged([[sph(.046), M(0, 0, 0)], [cyl(.042, .03, .28), M(0, -.14, 0)]]);
  const hp = [[new THREE.BoxGeometry(.07, .085, .028), M(0, -.325, 0)], [cyl(.01, .007, .06, 6), M(.045, -.33, .012, .3, 0, -.8)]];
  for (let i = 0; i < 4; i++) hp.push([cyl(.009, .006, .085, 6), M(-.027 + i * .018, -.4, .014, .45, 0, 0)]);
  GEO.hand = merged(hp);
  // extra facial structure takes its colour from the painted face right where it sits, so it blends in
  const SK = [.75, .45], S3 = (r, x, y, z, sx, sy, sz, u, v) => [sph(r, 10, 8), M(x, y, z, 0, 0, 0, sx, sy, sz), u === undefined ? SK : [u, v]];
  GEO.headZ = merged([[sph(.115, 30, 24), M(0, 0, 0, 0, 0, 0, .9, 1.2, 1)],
    S3(.02, 0, .008, .108, .55, 1.7, .8, .25, .53), S3(.0165, 0, -.016, .121, 1, .85, 1.05, .25, .49), S3(.0105, .0135, -.022, .113, 1, .8, 1, .27, .47), S3(.0105, -.0135, -.022, .113, 1, .8, 1, .23, .47),   // nose: bridge, tip, wings
    S3(.028, .04, .054, .088, 1.25, .38, .65, .31, .63), S3(.028, -.04, .054, .088, 1.25, .38, .65, .19, .63), S3(.018, 0, .05, .104, 1, .6, .6, .25, .63),   // brow ridge
    S3(.026, .064, -.014, .074, 1, .7, .8, .335, .44), S3(.026, -.064, -.014, .074, 1, .7, .8, .165, .44),   // cheekbones
    S3(.03, .103, 0, -.004, .3, 1, .68), S3(.03, -.103, 0, -.004, .3, 1, .68), S3(.012, .1, -.03, .002, .5, 1, .8), S3(.012, -.1, -.03, .002, .5, 1, .8)]);   // ears and lobes
  GEO.eyes = merged([[sph(.0145, 14, 10), M(.041, .027, .0885)], [sph(.0145, 14, 10), M(-.041, .027, .0885)]]);
  const Bx = (w, h, l) => new THREE.BoxGeometry(w, h, l), tp = [], cl = [], rb = [];
  GEO.jaw = merged([[sph(.052, 14, 10), M(0, -.028, .048, 0, 0, 0, .84, .4, 1.02)], [sph(.03, 10, 8), M(0, -.036, .084, 0, 0, 0, 1.15, .62, .8)], [sph(.026, 10, 8), M(0, -.046, .094, 0, 0, 0, 1.25, .8, .9)], [sph(.02, 8, 6), M(.04, -.03, .02, 0, 0, 0, .8, 1, 1.4)], [sph(.02, 8, 6), M(-.04, -.03, .02, 0, 0, 0, .8, 1, 1.4)]]);
  const tu = []; for (let i = 0; i < 8; i++) tu.push([new THREE.ConeGeometry(.0046, .015 + (i % 3) * .004, 4), M(-.0315 + i * .009, -.004, .103 - Math.abs(i - 3.5) * .0035, Math.PI, 0, 0)]);
  GEO.teethU = merged(tu); GEO.gumU = merged([[Bx(.074, .013, .016), M(0, .008, .098)]]); GEO.tongue = merged([[sph(.02, 8, 6), M(0, -.012, .06, 0, 0, 0, 1.1, .45, 1.9)]]);
  GEO.maw = merged([[sph(.034, 10, 8), M(0, -.004, .058, 0, 0, 0, 1, .55, 1.1)]]);
  for (let i = 0; i < 7; i++) tp.push([new THREE.ConeGeometry(.0048, .02 + (i % 2) * .008, 4), M(-.027 + i * .009, .0, .086 - Math.abs(i - 3) * .004)]);
  GEO.teeth = merged(tp);
  for (let i = 0; i < 4; i++) cl.push([new THREE.ConeGeometry(.0075, .085, 5), M(-.027 + i * .018, -.468, .04, Math.PI - .5, 0, 0)]); cl.push([new THREE.ConeGeometry(.007, .06, 5), M(.05, -.37, .03, Math.PI - .4, 0, -.8)]);
  GEO.claw = merged(cl);
  for (let i = 0; i < 5; i++) rb.push([Bx(.12, .013, .022), M(.055, .27 + i * .042, .122 - i * .005, 0, -.25, .18)]); rb.push([Bx(.016, .22, .02), M(-.012, .36, .12)]);
  GEO.ribs = merged(rb); GEO.gore = merged([[Bx(.15, .23, .012), M(.05, .355, .108, 0, -.2, 0)]]);
  GEO.hair = new THREE.SphereGeometry(.119, 14, 8, 0, Math.PI * 2, 0, Math.PI * .42); GEO.hair.scale(.92, 1.2, 1.02);
  GEO.helmet = new THREE.SphereGeometry(.125, 14, 8, 0, Math.PI * 2, 0, Math.PI * .55); GEO.helmet.scale(.98, 1.2, 1.08);
  const B = (w, h, l) => new THREE.BoxGeometry(w, h, l);
  GEO.vest = merged([[B(.43, .36, .28), M(0, .36, 0)], [B(.1, .12, .06), M(-.125, .26, .16)], [B(.1, .12, .06), M(0, .26, .16)], [B(.1, .12, .06), M(.125, .26, .16)], [B(.16, .1, .05), M(.09, .45, .155)],
    [B(.3, .4, .15), M(0, .4, -.21)], [B(.26, .1, .16), M(0, .64, -.2)], [B(.07, .08, .3), M(-.14, .6, 0)], [B(.07, .08, .3), M(.14, .6, 0)], [B(.44, .07, .3), M(0, .12, 0)], [B(.09, .14, .07), M(-.2, .1, .1)], [B(.08, .2, .1), M(.23, .02, 0)]]);

  const bump = bumpTex(), tones = ['#474d42', '#514f44', '#3a403b'];
  const skinT = base => canvasTex(256, (g, s) => {
    g.fillStyle = base; g.fillRect(0, 0, s, s); blotch(g, s, 44, '28,34,26', 6, 28, .55); blotch(g, s, 16, '112,114,92', 4, 16, .22); blotch(g, s, 10, '50,30,48', 6, 20, .3);
    veins(g, s, 14, 'rgba(38,28,52,.4)'); for (let i = 0; i < 4; i++) gash(g, Math.random() * s, Math.random() * s, rnd(6, 13)); blotch(g, s, 4, '70,6,4', 8, 24, .6); grainFx(g, s, 22);
  });
  const faceT = base => canvasTex(512, (g, s0) => { g.scale(2, 2); const s = 256;
    g.fillStyle = base; g.fillRect(0, 0, s, s); blotch(g, s, 40, '28,34,26', 6, 26, .5); blotch(g, s, 12, '50,30,48', 6, 18, .3); veins(g, s, 10, 'rgba(38,28,52,.4)');
    const cx = 64, sh = (x, y, r, c, a) => { const gr = g.createRadialGradient(x, y, 0, x, y, r); gr.addColorStop(0, `rgba(${c},${a})`); gr.addColorStop(1, `rgba(${c},0)`); g.fillStyle = gr; g.fillRect(x - r, y - r, r * 2, r * 2); };
    sh(cx - 24, 146, 17, '16,20,14', .6); sh(cx + 24, 146, 17, '16,20,14', .6); sh(cx, 96, 30, '20,22,16', .25);
    for (const sx of [-17, 17]) { sh(cx + sx, 112, 21, '85,18,14', .45); sh(cx + sx, 112, 20, '4,2,2', 1); sh(cx + sx, 112, 15, '0,0,0', 1); for (let i = 0; i < 3; i++) { const x = cx + sx + rnd(-6, 6), h = rnd(14, 40), gr = g.createLinearGradient(0, 118, 0, 118 + h); gr.addColorStop(0, 'rgba(8,2,2,.9)'); gr.addColorStop(1, 'rgba(8,2,2,0)'); g.fillStyle = gr; g.fillRect(x, 118, rnd(2, 4), h); } }
    g.strokeStyle = 'rgba(12,10,8,.75)'; g.lineWidth = 3; for (const sx of [-17, 17]) { g.beginPath(); g.moveTo(cx + sx - 13, 100 + (sx > 0 ? -3 : 2)); g.quadraticCurveTo(cx + sx, 94, cx + sx + 13, 100 + (sx > 0 ? 2 : -3)); g.stroke(); }
    g.fillStyle = 'rgba(10,6,5,.85)'; g.beginPath(); g.ellipse(cx - 4, 139, 2.6, 2, 0, 0, 7); g.ellipse(cx + 4, 139, 2.6, 2, 0, 0, 7); g.fill();
    sh(cx, 158, 26, '75,6,4', .55); sh(cx, 172, 42, '58,4,3', .65);
    g.fillStyle = '#0d0303'; g.beginPath(); g.ellipse(cx, 156, 17, 9 + Math.random() * 3, rnd(-.12, .12), 0, 7); g.fill();
    g.fillStyle = '#b3aa82'; for (let i = -3; i <= 3; i++) { if (Math.random() < .2) continue; g.fillRect(cx + i * 4.3 - 1.6, 149 + Math.abs(i) * .7, 3.1, rnd(3, 5)); g.fillRect(cx + i * 4.1 - 1.5, 160 - Math.abs(i) * .6, 2.9, rnd(2.5, 4.5)); }
    for (let i = 0; i < 5; i++) { const x = cx + rnd(-14, 14), h = rnd(18, 60), gr = g.createLinearGradient(0, 162, 0, 162 + h); gr.addColorStop(0, 'rgba(70,4,3,.9)'); gr.addColorStop(1, 'rgba(70,4,3,0)'); g.fillStyle = gr; g.fillRect(x, 162, rnd(2, 6), h); }
    gash(g, cx + rnd(-30, 30), rnd(60, 90), rnd(7, 12)); gash(g, rnd(120, 240), rnd(60, 200), rnd(8, 14));
    g.strokeStyle = 'rgba(14,11,8,.8)'; g.lineWidth = 1.2; for (let i = 0; i < 260; i++) { const x = Math.random() * s, y = Math.random() * 46; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-3, 3), y + rnd(4, 14)); g.stroke(); }
    // brow furrows, crow's feet, folds from the nose to the mouth, bruised bags under the eyes
    g.strokeStyle = 'rgba(14,12,9,.55)'; g.lineWidth = 1; for (let i = 0; i < 5; i++) { const y = 70 + i * 5 + rnd(-1, 1); g.beginPath(); g.moveTo(cx - 26, y + 2); g.quadraticCurveTo(cx, y - 3 - i * .4, cx + 26, y + 2); g.stroke(); }
    for (const sx of [-1, 1]) { g.beginPath(); g.moveTo(cx + sx * 7, 138); g.quadraticCurveTo(cx + sx * 15, 148, cx + sx * 20, 164); g.stroke(); g.beginPath(); g.moveTo(cx + sx * 3, 98); g.lineTo(cx + sx * 4, 108); g.stroke();
      for (let i = 0; i < 3; i++) { g.beginPath(); g.moveTo(cx + sx * 31, 110 + i * 2); g.lineTo(cx + sx * 38, 106 + i * 5); g.stroke(); }
      g.strokeStyle = 'rgba(60,30,62,.5)'; g.lineWidth = 2; g.beginPath(); g.arc(cx + sx * 17, 113, 15, .5, 2.6); g.stroke(); g.strokeStyle = 'rgba(14,12,9,.55)'; g.lineWidth = 1; }
    // a patch where the skin has come away: wet muscle with fibres running through it
    { const px = cx + (Math.random() < .5 ? -1 : 1) * rnd(22, 30), py = rnd(126, 150), pr = rnd(8, 13); g.save(); g.beginPath(); for (let i = 0; i < 11; i++) { const a = i / 11 * 6.283, rr = pr * rnd(.6, 1.2); g.lineTo(px + Math.cos(a) * rr, py + Math.sin(a) * rr * 1.3); } g.closePath(); g.fillStyle = '#4a0806'; g.fill(); g.clip();
      g.strokeStyle = 'rgba(140,30,20,.7)'; g.lineWidth = .8; for (let i = 0; i < 16; i++) { const x = px - pr + i * pr / 8; g.beginPath(); g.moveTo(x, py - pr * 1.4); g.lineTo(x + rnd(-3, 3), py + pr * 1.4); g.stroke(); } g.restore();
      g.strokeStyle = 'rgba(190,180,150,.45)'; g.lineWidth = 1.2; g.beginPath(); g.arc(px, py, pr * 1.05, rnd(0, 3), rnd(3.5, 6)); g.stroke(); }
    // lipless mouth: gum line and stained teeth
    g.fillStyle = 'rgba(96,14,10,.9)'; g.fillRect(cx - 15, 146, 30, 3.5); g.fillRect(cx - 14, 163, 28, 3);
    g.strokeStyle = 'rgba(30,20,8,.8)'; g.lineWidth = .6; for (let i = -3; i <= 4; i++) { g.beginPath(); g.moveTo(cx + i * 4.3 - 2.1, 148); g.lineTo(cx + i * 4.3 - 2.1, 165); g.stroke(); }
    for (let i = 0; i < 1400; i++) { g.fillStyle = `rgba(${Math.random() < .6 ? '12,14,10' : '150,150,120'},${rnd(.08, .3)})`; g.fillRect(Math.random() * 128, rnd(40, 200), .7, .7); }   // pores and mottling
    veins(g, 128, 6, 'rgba(50,26,70,.5)');
    g.setTransform(1, 0, 0, 1, 0, 0); grainFx(g, s0, 16);
  });
  const weave = (g, s) => { g.fillStyle = 'rgba(0,0,0,.09)'; for (let y = 0; y < s; y += 3) g.fillRect(0, y, s, 1); g.fillStyle = 'rgba(255,255,255,.03)'; for (let x = 0; x < s; x += 3) g.fillRect(x, 0, 1, s); };
  const shirtT = col => canvasTex(256, (g, s) => {
    g.fillStyle = col; g.fillRect(0, 0, s, s); weave(g, s); blotch(g, s, 30, '10,9,7', 8, 36, .6);
    for (let i = 0; i < 6; i++) tearBlob(g, Math.random() * s, rnd(.3, .82) * s, rnd(9, 24), tones[1]);
    const bx0 = s / 2 + rnd(-20, 20), gr = g.createRadialGradient(bx0, s * .42, 0, bx0, s * .42, 60); gr.addColorStop(0, 'rgba(70,5,3,.92)'); gr.addColorStop(.6, 'rgba(60,4,3,.7)'); gr.addColorStop(1, 'rgba(60,4,3,0)'); g.fillStyle = gr; g.fillRect(0, 0, s, s);
    for (let i = 0; i < 8; i++) { const x = bx0 + rnd(-40, 40), h = rnd(30, 110), g2 = g.createLinearGradient(0, s * .42, 0, s * .42 + h); g2.addColorStop(0, 'rgba(62,4,3,.85)'); g2.addColorStop(1, 'rgba(62,4,3,0)'); g.fillStyle = g2; g.fillRect(x, s * .42, rnd(3, 8), h); }
    g.fillStyle = tones[1]; g.fillRect(0, 0, s, s * .19); for (let x = 0; x < s; x += 5) g.fillRect(x, s * .19, 5, rnd(0, 9));
    blotch(g, s, 8, '28,34,26', 6, 20, .5); g.fillStyle = '#17181a'; g.fillRect(0, s * .9, s, s * .1); grainFx(g, s, 28);
  });
  const pantsT = col => canvasTex(256, (g, s) => {
    g.fillStyle = col; g.fillRect(0, 0, s, s); weave(g, s); blotch(g, s, 40, '10,9,7', 8, 40, .6); for (let i = 0; i < 4; i++) tearBlob(g, Math.random() * s, Math.random() * s, rnd(8, 18), tones[0]);
    blotch(g, s, 5, '62,5,3', 12, 40, .65); blotch(g, s, 12, '55,45,30', 10, 30, .35); grainFx(g, s, 30);
  });
  MAT.zSkin = tones.map(c => new THREE.MeshStandardMaterial({ map: skinT(c), bumpMap: bump, bumpScale: .006, roughness: .62 }));
  MAT.zFace = tones.map(c => new THREE.MeshStandardMaterial({ map: faceT(c), bumpMap: bump, bumpScale: .004, roughness: .6 }));
  MAT.zShirt = ['#4d5054', '#3a4232', '#4a3a2e', '#5b5a50', '#2a303a', '#5a2f2c'].map(c => new THREE.MeshStandardMaterial({ map: shirtT(c), bumpMap: bump, bumpScale: .008, roughness: .95 }));
  MAT.zPants = ['#23262b', '#2e2a22', '#323830'].map(c => new THREE.MeshStandardMaterial({ map: pantsT(c), bumpMap: bump, bumpScale: .008, roughness: .95 }));
  MAT.hair = new THREE.MeshStandardMaterial({ color: 0x120f0c, roughness: 1 });
  MAT.zBloat = new THREE.MeshStandardMaterial({ map: MAT.zSkin[0].map, color: 0xc6e88a, emissive: 0x0a1803, bumpMap: bump, bumpScale: .01, roughness: .45 }); MAT.zBloat.color.convertSRGBToLinear();
  MAT.zArmor = new THREE.MeshStandardMaterial({ color: 0x24282c, roughness: .6, metalness: .1 }); MAT.zArmor.color.convertSRGBToLinear();
  MAT.dark = new THREE.MeshStandardMaterial({ color: 0x0b0806, roughness: .9 });
  // eyeballs: clouded iris, pinprick pupil, burst vessels. Unlit, so they still catch in the dark.
  const eyeT = (white, iris) => canvasTex(64, (g, s) => { g.fillStyle = white; g.fillRect(0, 0, s, s); const x = s * .25, y = s * .5;
    g.strokeStyle = 'rgba(150,16,8,.6)'; g.lineWidth = .7; for (let i = 0; i < 14; i++) { const a = rnd(0, 6.283); g.beginPath(); g.moveTo(x + Math.cos(a) * s * .2, y + Math.sin(a) * s * .4); g.quadraticCurveTo(x + Math.cos(a + .4) * s * .13, y + Math.sin(a + .4) * s * .26, x + Math.cos(a) * s * .08, y + Math.sin(a) * s * .16); g.stroke(); }
    g.fillStyle = iris; g.beginPath(); g.ellipse(x, y, s * .075, s * .15, 0, 0, 7); g.fill(); g.strokeStyle = 'rgba(0,0,0,.5)'; g.lineWidth = 1; g.stroke();
    g.fillStyle = '#040404'; g.beginPath(); g.ellipse(x, y, s * .024, s * .048, 0, 0, 7); g.fill(); g.fillStyle = 'rgba(255,255,255,.75)'; g.fillRect(x + 2, y - 5, 1.5, 3); });
  MAT.eye = new THREE.MeshBasicMaterial({ map: eyeT('#a8a290', '#7c8878'), color: 0xb0b0b0 }); MAT.eyeR = new THREE.MeshBasicMaterial({ map: eyeT('#6a0c06', '#ff3a18') }); MAT.eyeG = new THREE.MeshBasicMaterial({ map: eyeT('#3c5c18', '#b8ff50') });
  MAT.bone = new THREE.MeshStandardMaterial({ color: 0x8c8262, roughness: .6 }); MAT.gore = new THREE.MeshStandardMaterial({ color: 0x2a0403, roughness: .25 }); MAT.bone.color.convertSRGBToLinear(); MAT.gore.color.convertSRGBToLinear();
  MAT.gear = new THREE.MeshStandardMaterial({ color: 0x2c3327, roughness: .9 }); MAT.gearC = [0x4a5a3c, 0x34507a, 0x7a3a30, 0x7a6c38].map(c => new THREE.MeshStandardMaterial({ color: c, roughness: .9 })); MAT.gear2 = new THREE.MeshStandardMaterial({ color: 0x33373a, roughness: .8 });
  MAT.pskin = new THREE.MeshStandardMaterial({ color: 0x9a7a66, roughness: .8 });
  for (const m of [MAT.gear, MAT.gear2, MAT.pskin, MAT.hair].concat(MAT.gearC)) m.color.convertSRGBToLinear();
  MAT.pface = new THREE.MeshStandardMaterial({ map: canvasTex(512, (g, s0) => { g.scale(2, 2); const s = 256, cx = 64; g.fillStyle = '#9a7660'; g.fillRect(0, 0, s, s); blotch(g, s, 26, '70,48,38', 8, 30, .28); blotch(g, s, 14, '176,124,104', 6, 20, .16);
    const sh = (x, y, r, c, a) => { const gr = g.createRadialGradient(x, y, 0, x, y, r); gr.addColorStop(0, `rgba(${c},${a})`); gr.addColorStop(1, `rgba(${c},0)`); g.fillStyle = gr; g.fillRect(x - r, y - r, r * 2, r * 2); };
    sh(cx - 23, 140, 16, '130,62,52', .22); sh(cx + 23, 140, 16, '130,62,52', .22); sh(cx, 150, 34, '60,40,32', .16); sh(cx, 92, 30, '190,140,116', .14);
    for (const sx of [-17, 17]) { sh(cx + sx, 111, 15, '52,30,24', .6);
      g.fillStyle = '#e6e2da'; g.beginPath(); g.ellipse(cx + sx, 112, 7.5, 3.8, 0, 0, 7); g.fill(); sh(cx + sx - 6, 112, 4, '150,60,50', .3);
      const ir = g.createRadialGradient(cx + sx, 112, .4, cx + sx, 112, 3.7); ir.addColorStop(0, '#060504'); ir.addColorStop(.36, '#060504'); ir.addColorStop(.46, '#5a3c22'); ir.addColorStop(1, '#22140a'); g.fillStyle = ir; g.beginPath(); g.arc(cx + sx, 112, 3.7, 0, 7); g.fill();
      g.fillStyle = 'rgba(255,255,255,.85)'; g.fillRect(cx + sx + 1, 110.3, 1.1, 1.1);
      g.strokeStyle = '#24140c'; g.lineWidth = 1.5; g.beginPath(); g.moveTo(cx + sx - 8.5, 113); g.quadraticCurveTo(cx + sx, 106.2, cx + sx + 8.5, 113); g.stroke();
      g.strokeStyle = 'rgba(70,40,30,.6)'; g.lineWidth = .8; g.beginPath(); g.moveTo(cx + sx - 7.5, 113.6); g.quadraticCurveTo(cx + sx, 117.4, cx + sx + 7.5, 113.6); g.stroke(); g.beginPath(); g.moveTo(cx + sx - 8, 108.5); g.quadraticCurveTo(cx + sx, 103.6, cx + sx + 8, 108.5); g.stroke();
      g.strokeStyle = '#26170e'; g.lineWidth = .9; for (let i = 0; i < 30; i++) { const x = cx + sx - 11.5 + i * .78, y = 100.5 + Math.abs(i - 15) * .14; g.beginPath(); g.moveTo(x, y + 2.6); g.lineTo(x + (sx > 0 ? 1.3 : -1.3), y - 1.4 + rnd(-.7, .7)); g.stroke(); } }
    g.strokeStyle = 'rgba(56,32,24,.55)'; g.lineWidth = 1.3; for (const sx of [-1, 1]) { g.beginPath(); g.moveTo(cx + sx * 3, 117); g.quadraticCurveTo(cx + sx * 4, 130, cx + sx * 7.5, 138); g.quadraticCurveTo(cx + sx * 7, 142, cx + sx * 3, 141); g.stroke(); g.beginPath(); g.moveTo(cx + sx * 8, 140); g.quadraticCurveTo(cx + sx * 14, 148, cx + sx * 15, 158); g.stroke(); }
    g.fillStyle = 'rgba(28,14,10,.85)'; g.beginPath(); g.ellipse(cx - 3.6, 140, 2.2, 1.3, .3, 0, 7); g.ellipse(cx + 3.6, 140, 2.2, 1.3, -.3, 0, 7); g.fill(); sh(cx, 133, 5, '220,170,150', .25);
    g.fillStyle = '#7c4438'; g.beginPath(); g.moveTo(cx - 11, 156); g.quadraticCurveTo(cx - 4, 151.5, cx, 153.5); g.quadraticCurveTo(cx + 4, 151.5, cx + 11, 156); g.quadraticCurveTo(cx, 157.5, cx - 11, 156); g.fill();
    g.fillStyle = '#8c5044'; g.beginPath(); g.moveTo(cx - 11, 156); g.quadraticCurveTo(cx, 164.5, cx + 11, 156); g.quadraticCurveTo(cx, 158, cx - 11, 156); g.fill(); g.strokeStyle = '#34181a'; g.lineWidth = 1; g.beginPath(); g.moveTo(cx - 11.5, 156); g.quadraticCurveTo(cx, 158, cx + 11.5, 156); g.stroke(); sh(cx, 167, 8, '50,30,24', .3);
    for (let i = 0; i < 1500; i++) { g.fillStyle = `rgba(30,22,18,${rnd(.2, .5)})`; g.fillRect(cx + rnd(-30, 30), rnd(143, 192), .9, rnd(.9, 1.8)); }   // stubble
    for (let i = 0; i < 900; i++) { g.fillStyle = `rgba(${Math.random() < .5 ? '60,36,28' : '210,170,150'},${rnd(.06, .2)})`; g.fillRect(Math.random() * 128, rnd(40, 200), .7, .7); }
    g.strokeStyle = 'rgba(60,36,28,.35)'; g.lineWidth = .8; for (let i = 0; i < 3; i++) { g.beginPath(); g.moveTo(cx - 22, 76 + i * 6); g.quadraticCurveTo(cx, 73 + i * 6, cx + 22, 76 + i * 6); g.stroke(); }
    blotch(g, s, 6, '20,16,12', 6, 18, .3); sh(cx + 21, 128, 5, '90,20,16', .5); g.setTransform(1, 0, 0, 1, 0, 0); grainFx(g, s0, 10); }), bumpMap: bump, bumpScale: .0025, roughness: .72 });
  // gun + arm materials
  const scr = canvasTex(256, (g, s) => { g.fillStyle = '#808080'; g.fillRect(0, 0, s, s); for (let i = 0; i < 900; i++) { g.strokeStyle = `rgba(${Math.random() < .5 ? '255,255,255' : '0,0,0'},${rnd(.05, .3)})`; g.lineWidth = rnd(.4, 1.2);
    const x = Math.random() * s, y = Math.random() * s, a = rnd(-.25, .25) + (Math.random() < .12 ? rnd(0, 3) : 0), l = rnd(6, 60); g.beginPath(); g.moveTo(x, y); g.lineTo(x + Math.cos(a) * l, y + Math.sin(a) * l); g.stroke(); } grainFx(g, s, 30); }, false);
  const metalT = base => canvasTex(512, (g, s) => { g.fillStyle = base; g.fillRect(0, 0, s, s);
    for (let i = 0; i < 1600; i++) { g.fillStyle = `rgba(${Math.random() < .5 ? '255,255,255' : '0,0,0'},${rnd(.015, .07)})`; g.fillRect(Math.random() * s, Math.random() * s, rnd(10, 140), 1); }
    blotch(g, s, 40, '150,152,156', 2, 10, .28); blotch(g, s, 24, '0,0,0', 14, 60, .32); blotch(g, s, 10, '70,40,20', 6, 22, .16);
    for (let i = 0; i < 60; i++) { g.strokeStyle = `rgba(200,202,206,${rnd(.1, .35)})`; g.lineWidth = rnd(.5, 1.3); const x = Math.random() * s, y = Math.random() * s; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-30, 30), y + rnd(-6, 6)); g.stroke(); } grainFx(g, s, 12); });
  MAT.gMetal = new THREE.MeshStandardMaterial({ map: metalT('#2a2d30'), bumpMap: scr, bumpScale: .0007, metalness: .85, roughness: .42, envMapIntensity: .9 });
  MAT.gSteel = new THREE.MeshStandardMaterial({ map: metalT('#8c9094'), bumpMap: scr, bumpScale: .0006, metalness: .95, roughness: .3, envMapIntensity: 1.1 });
  MAT.gPoly = new THREE.MeshStandardMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#1b1c1d'; g.fillRect(0, 0, s, s); blotch(g, s, 20, '60,60,58', 2, 8, .18); grainFx(g, s, 22); }), bumpMap: bump, bumpScale: .0015, metalness: .1, roughness: .72, envMapIntensity: .5 });
  MAT.gWood = new THREE.MeshStandardMaterial({ map: canvasTex(512, (g, s) => { g.fillStyle = '#4a2c16'; g.fillRect(0, 0, s, s);
    for (let i = 0; i < 280; i++) { const y = Math.random() * s, a = rnd(2, 9), ph = rnd(0, 6); g.strokeStyle = `rgba(${rnd(8, 120) | 0},${rnd(6, 62) | 0},10,${rnd(.15, .4)})`; g.lineWidth = rnd(.6, 2.4); g.beginPath(); for (let x = 0; x <= s; x += 16) g.lineTo(x, y + Math.sin(x * .012 + ph) * a); g.stroke(); }
    for (let i = 0; i < 5; i++) { const x = Math.random() * s, y = Math.random() * s; for (let r = 14; r > 2; r -= 2.5) { g.strokeStyle = `rgba(20,10,4,${.5 - r * .025})`; g.lineWidth = 1.2; g.beginPath(); g.ellipse(x, y, r * 2, r, 0, 0, 7); g.stroke(); } }
    blotch(g, s, 10, '15,8,4', 20, 80, .35); blotch(g, s, 12, '120,80,40', 4, 14, .15); grainFx(g, s, 14); }), bumpMap: scr, bumpScale: .0012, roughness: .42, metalness: 0, envMapIntensity: .6 });
  MAT.gSleeve = new THREE.MeshStandardMaterial({ map: canvasTex(256, (g, s) => { g.fillStyle = '#3b4230'; g.fillRect(0, 0, s, s); blotch(g, s, 30, '28,32,22', 12, 40, .8); blotch(g, s, 22, '70,66,46', 10, 30, .55); blotch(g, s, 16, '18,18,14', 8, 26, .7); weave(g, s); grainFx(g, s, 26); }), bumpMap: bump, bumpScale: .004, roughness: 1, envMapIntensity: .1 });
  MAT.gGlove = new THREE.MeshStandardMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#141414'; g.fillRect(0, 0, s, s); blotch(g, s, 20, '50,48,44', 3, 12, .25); grainFx(g, s, 26); }), bumpMap: bump, bumpScale: .002, roughness: .6, envMapIntensity: .4 });
  MAT.gGlass = new THREE.MeshStandardMaterial({ color: 0x3a6a90, transparent: true, opacity: .22, metalness: 1, roughness: .05, depthWrite: false });
  MAT.gDark = new THREE.MeshStandardMaterial({ color: 0x050505, roughness: .9 });
}
function buildHumanoid(o) {
  const g = new THREE.Group(), body = new THREE.Group(); g.add(body);
  const mk = (geo, mat, par, x, y, z) => { const m = new THREE.Mesh(geo, mat); m.position.set(x || 0, y || 0, z || 0); m.castShadow = true; par.add(m); return m; };
  const legs = [], shins = [], arms = [], fore = []; let jaw = null;
  for (const s of [-1, 1]) {
    const leg = new THREE.Group(); leg.position.set(s * .1, .92, 0); body.add(leg); mk(GEO.thigh, o.pants, leg);
    const shin = new THREE.Group(); shin.position.y = -.46; leg.add(shin); mk(GEO.shin, o.pants, shin); mk(GEO.foot, o.shoe, shin);
    legs.push(leg); shins.push(shin);
  }
  const torso = new THREE.Group(); torso.position.y = .92; body.add(torso); mk(GEO.torso, o.cloth, torso);
  const head = new THREE.Group(); head.position.set(0, .74, .015); torso.add(head);
  const skull = mk(GEO.headZ, o.face, head, 0, .135, 0); skull.userData.head = true;
  if (o.player) { const S = o.S, m = S.m, hat = S.hat; mk(GEO.vest, m.vest, torso);
    if (!GEO.brim) { GEO.brim = new THREE.BoxGeometry(.2, .016, .13); GEO.hood = new THREE.SphereGeometry(.152, 14, 10); GEO.hood.scale(1, 1.16, 1.06); GEO.visor = new THREE.BoxGeometry(.19, .085, .1); GEO.plate = new THREE.BoxGeometry(.11, .075, .03); GEO.can = new THREE.CylinderGeometry(.035, .035, .07, 10); GEO.can.rotateX(Math.PI / 2); }
    if (hat === 'helmet' || hat === 'riot') mk(GEO.helmet, m.head, head, 0, .15, 0);
    if (hat === 'riot') mk(GEO.visor, MAT.gGlass || MAT.gDark, head, 0, .15, .1);
    if (hat === 'cap') { mk(GEO.helmet, m.head, head, 0, .175, 0).scale.set(1, .62, 1); mk(GEO.brim, m.head, head, 0, .2, .14); }
    if (hat === 'beanie') mk(GEO.helmet, m.cloth, head, 0, .16, 0).scale.set(1.02, .9, 1.02);
    if (hat === 'hood') { mk(GEO.hood, m.cloth, head, 0, .135, 0); mk(GEO.visor, MAT.gDark, head, 0, .16, .105); mk(GEO.can, MAT.gDark, head, 0, .07, .15); }
    if (hat === 'mask') { mk(GEO.hood, m.head, head, 0, .135, 0).scale.setScalar(.93); mk(GEO.plate, MAT.bone, head, 0, .1, .135); }
    if (hat === 'bare') mk(GEO.hair, MAT.hair, head, 0, .138, 0); }
  else { const e = mk(GEO.eyes, o.eye || MAT.eye, head, 0, .135, 0); e.castShadow = false; e.userData.head = true; if (o.hair) mk(GEO.hair, MAT.hair, head, 0, .138, 0).userData.head = true;
    jaw = new THREE.Group(); jaw.position.set(0, .064, 0); head.add(jaw); mk(GEO.jaw, o.skin, jaw).userData.head = true; mk(GEO.maw, MAT.gDark, jaw).userData.head = true; mk(GEO.teeth, MAT.bone, jaw).userData.head = true; mk(GEO.tongue, MAT.gore, jaw).userData.head = true;
    mk(GEO.teethU, MAT.bone, head, 0, .07, 0).userData.head = true; mk(GEO.gumU, MAT.gore, head, 0, .07, 0).userData.head = true; }
  for (const s of [-1, 1]) {
    const arm = new THREE.Group(); arm.position.set(s * .235, .56, 0); torso.add(arm); mk(GEO.upper, o.cloth, arm);
    const f = new THREE.Group(); f.position.y = -.32; arm.add(f); mk(GEO.fore, o.skin, f); mk(GEO.hand, o.skin, f).scale.x = s; if (!o.player) { mk(GEO.claw, MAT.bone, f); arm.scale.y = 1.12; }
    arms.push(arm); fore.push(f);
  }
  return { g, body, torso, head, skull, jaw, legs, shins, arms, fore, ph: 0, lastAtk: 0 };
}
function makeZombieView(z) {
  const R = seeded(z.id * 7919 + 13), tone = (R() * 3) | 0, ty = z.type || 'walker', bl = ty === 'bloater';
  const v = buildHumanoid({ skin: bl ? MAT.zBloat : MAT.zSkin[tone], face: MAT.zFace[tone], cloth: bl ? MAT.zBloat : MAT.zShirt[ty === 'brute' ? 5 : (R() * 6) | 0], pants: MAT.zPants[(R() * 3) | 0], shoe: R() < .4 ? MAT.zSkin[tone] : MAT.dark, hair: ty !== 'armored' && R() < .6, eye: ty === 'runner' || ty === 'brute' ? MAT.eyeR : bl ? MAT.eyeG : MAT.eye });
  if (!bl && ty !== 'armored' && R() < .55) { for (const q of [[GEO.gore, MAT.gore], [GEO.ribs, MAT.bone]]) { const m = new THREE.Mesh(q[0], q[1]); m.castShadow = true; v.torso.add(m); } }
  v.limp = R() < .3 ? 1 : 0; v.armDown = R() < .25 ? (R() < .5 ? 0 : 1) : -1; v.tw = R() * 10; v.gy = z.y || 0;
  if (R() < .16 && ty !== 'crawler') v.fore[R() < .5 ? 0 : 1].visible = false;
  const sc = .94 + R() * .14; let sx = sc * (.92 + R() * .2), sy = sc, sz = sc * (.95 + R() * .15);
  if (ty === 'armored') { for (const q of [[GEO.helmet, v.head, .15], [GEO.vest, v.torso, 0]]) { const m = new THREE.Mesh(q[0], MAT.zArmor); m.position.y = q[2]; m.castShadow = true; q[1].add(m); } v.armDown = -1; }
  if (ty === 'crawler') { v.crawl = 1; v.legs.forEach(l => { l.visible = false; }); v.limp = 0; v.armDown = -1; }
  if (ty === 'runner') { v.run = 1; v.limp = 0; v.armDown = -1; sx *= .86; sz *= .9; }
  if (ty === 'brute') { sx *= 1.5; sy *= 1.4; sz *= 1.45; v.limp = 0; }
  if (bl) { sx *= 1.5; sz *= 1.6; sy *= 1.04; }
  v.g.scale.set(sx, sy, sz); v.neck = R() < .3 && !bl ? (R() - .5) * 1.3 : 0; v.sp = 0;
  v.g.traverse(o => { if (o.isMesh) o.userData.zr = z; });
  v.g.position.set(z.x, (z.y || 0) - 1.9, z.z); zGroup.add(v.g); z.view = v;
}
function makePlayerView(p) {
  const S = skinOf(p.sk), v = buildHumanoid({ skin: MAT.gGlove, face: MAT.pface, cloth: S.m.cloth, pants: S.m.pants, shoe: MAT.dark, player: true, S });
  const gun = buildGun(p.wid === 'pistol' ? 'rifle' : p.wid, false); gun.rotation.y = Math.PI; gun.position.set(.08, .5, .4); v.torso.add(gun);
  v.arms[0].rotation.x = -1.25; v.arms[0].rotation.z = -.35; v.arms[1].rotation.x = -1.1; v.arms[1].rotation.z = .25;
  const c = document.createElement('canvas'); c.width = 256; c.height = 64; const g = c.getContext('2d');
  g.font = '700 30px Arial'; g.textAlign = 'center'; g.fillStyle = ['#d8e6c0', '#b8d0f4', '#f4c0b4', '#f0e2a0'][p.ci | 0] || '#d8e6c0'; g.shadowColor = '#000'; g.shadowBlur = 6; g.fillText(p.name || 'Player', 128, 42);
  const sp = new THREE.Sprite(new THREE.SpriteMaterial({ map: new THREE.CanvasTexture(c), transparent: true, depthWrite: false })); sp.scale.set(1.3, .32, 1); sp.position.y = 2.1; v.g.add(sp);
  v.g.position.set(p.x, 0, p.z); scene.add(v.g); p.view = v; v.seq = p.fireSeq;
}

// ---------------------------------------------------------------- gun models
const GUNDEF = {
  smg:     { rl: .2,  hg: .13, hgR: .024, brl: .05, brlR: .008,  stock: 'tube',  stockL: .17, mag: 'stick',    optic: 'iron' },
  shotgun: { rl: .22, hg: .26, hgR: .024, brl: .3,  brlR: .0115, stock: 'wood',  stockL: .26, mag: null,       optic: 'bead', pump: true },
  rifle:   { rl: .22, hg: .27, hgR: .027, brl: .14, brlR: .009,  stock: 'solid', stockL: .22, mag: 'curved',   optic: 'iron' },
  dmr:     { rl: .25, hg: .32, hgR: .026, brl: .24, brlR: .0095, stock: 'solid', stockL: .26, mag: 'straight', optic: 'scope' },
  lmg:     { rl: .28, hg: .26, hgR: .03,  brl: .22, brlR: .011,  stock: 'solid', stockL: .22, mag: 'box',      optic: 'iron', bipod: true },
  mac:     { rl: .17, hg: .04, hgR: .021, brl: .05, brlR: .009,  stock: 'tube',  stockL: .12, mag: 'stick',    optic: 'iron', magZ: 2 },
  mp5:     { rl: .2,  hg: .15, hgR: .025, brl: .03, brlR: .008,  stock: 'solid', stockL: .19, mag: 'curved',   optic: 'iron' },
  ak:      { rl: .22, hg: .2,  hgR: .026, brl: .2,  brlR: .0085, stock: 'wood',  stockL: .24, mag: 'curved',   optic: 'iron', hgWood: 1, pg: 1 },
  m16:     { rl: .22, hg: .3,  hgR: .028, brl: .16, brlR: .009,  stock: 'solid', stockL: .25, mag: 'straight', optic: 'iron', carry: 1 },
  bullpup: { rl: .3,  hg: .14, hgR: .026, brl: .1,  brlR: .009,  stock: 'solid', stockL: .1,  mag: 'curved',   optic: 'iron', magZ: 1, carry: 1 },
  autoshot:{ rl: .22, hg: .24, hgR: .027, brl: .26, brlR: .0115, stock: 'solid', stockL: .22, mag: null,       optic: 'iron' },
  dbl:     { rl: .16, hg: .2,  hgR: .025, brl: .34, brlR: .011,  stock: 'wood',  stockL: .26, mag: null,       optic: 'iron', hgWood: 1, dbl: 1 },
  sniper:  { rl: .26, hg: .3,  hgR: .024, brl: .38, brlR: .0095, stock: 'wood',  stockL: .28, mag: 'straight', optic: 'scope', hgWood: 1, bolt: 1 },
  lever:   { rl: .2,  hg: .24, hgR: .024, brl: .26, brlR: .009,  stock: 'wood',  stockL: .26, mag: null,       optic: 'iron', hgWood: 1 },
  pdw:     { rl: .19, hg: .09, hgR: .026, brl: .03, brlR: .009,  stock: 'tube',  stockL: .14, mag: 'straight', optic: 'iron' },
  battle:  { rl: .24, hg: .3,  hgR: .027, brl: .2,  brlR: .0095, stock: 'solid', stockL: .25, mag: 'straight', optic: 'scope' },
  carbine: { rl: .21, hg: .3,  hgR: .031, brl: .02, brlR: .014,  stock: 'tube',  stockL: .18, mag: 'curved',   optic: 'iron' },
  hmg:     { rl: .3,  hg: .3,  hgR: .032, brl: .3,  brlR: .0125, stock: 'solid', stockL: .22, mag: 'box',      optic: 'iron', bipod: true, carry: 1 },
  minigun: { rl: .26, hg: .34, hgR: .04,  brl: .1,  brlR: .016,  stock: 'tube',  stockL: .08, mag: 'box',      optic: 'iron' },
  launcher:{ rl: .16, hg: .2,  hgR: .036, brl: .08, brlR: .024,  stock: 'solid', stockL: .2,  mag: null,       optic: 'iron' }
};
function buildGun(id, withArms) {
  const P = {}, add = (k, geo, m) => { (P[k] = P[k] || []).push([geo, m]); };
  const bx = (k, w, h, l, x, y, z, rx, ry, rz) => add(k, new THREE.BoxGeometry(w, h, l), M(x, y, z, rx, ry, rz));
  const cz = (k, rBack, rFront, len, x, y, z, n, open) => add(k, new THREE.CylinderGeometry(rBack, rFront, len, n || 14, 1, !!open), M(x, y, z, Math.PI / 2, 0, 0));
  const sp = (k, r, x, y, z, sx, sy, sz) => add(k, new THREE.SphereGeometry(r, 10, 8), M(x, y, z, 0, 0, 0, sx, sy, sz));
  const seg = (k, rA, rB, A, B, n) => { const a = V3(A[0], A[1], A[2]), b = V3(B[0], B[1], B[2]), d = b.clone().sub(a), len = d.length();
    const q = new THREE.Quaternion().setFromUnitVectors(V3(0, 1, 0), d.normalize()); add(k, new THREE.CylinderGeometry(rB, rA, len, n || 10), new THREE.Matrix4().compose(a.add(b).multiplyScalar(.5), q, V3(1, 1, 1))); };
  let muzzleZ, sightY, grip, fore = null, adsZ = .1, by = .012;
  const vid = id; if (WEAPONS[id] && WEAPONS[id].base) id = WEAPONS[id].base;
  if (id === 'pistol') {
    by = .02; adsZ = -.08;
    bx('Metal', .028, .03, .19, 0, .02, -.01); for (let i = 0; i < 6; i++) bx('Dark', .0292, .022, .003, 0, .02, .048 + i * .0065);
    bx('Dark', .002, .012, .035, .0145, .026, -.03); cz('Metal', .0075, .0075, .014, 0, .02, -.108, 10); cz('Dark', .0045, .0045, .016, 0, .02, -.108, 8);
    bx('Poly', .027, .022, .165, 0, -.005, -.008); bx('Poly', .022, .008, .05, 0, -.018, -.07);
    bx('Poly', .028, .098, .046, 0, -.06, .055, .22); bx('Metal', .026, .008, .048, 0, -.11, .067, .22);
    bx('Poly', .01, .004, .05, 0, -.042, -.002); bx('Poly', .01, .03, .004, 0, -.029, -.027); bx('Metal', .004, .018, .005, 0, -.028, .004, -.35);
    bx('Metal', .004, .008, .006, 0, .039, -.095); bx('Metal', .006, .009, .008, .008, .0395, .075); bx('Metal', .006, .009, .008, -.008, .0395, .075);
    bx('Metal', .012, .014, .012, 0, .022, .09);
    muzzleZ = -.115; sightY = .046; grip = [0, -.06, .055];
    bx('Steel', .0015, .012, .03, .0148, .026, -.03); bx('Steel', .003, .005, .03, .0155, .004, 0); bx('Steel', .004, .006, .006, .0148, -.02, .03); cz('Steel', .0055, .0055, .002, 0, .02, -.1065, 10); for (let i = 0; i < 5; i++) bx('Dark', .0286, .004, .03, 0, -.032 - i * .014, .051 + i * .0032, .22);
    if (vid === 'autopistol') { bx('Metal', .022, .075, .034, 0, -.15, .077, .22); bx('Metal', .008, .012, .05, 0, .04, .02); }
    if (vid === 'handcannon') { bx('Metal', .033, .038, .07, 0, .02, -.14); for (let i = 0; i < 3; i++) bx('Dark', .034, .012, .006, 0, .034, -.158 + i * .016); bx('Metal', .004, .008, .006, 0, .043, -.165); muzzleZ = -.178; }
  } else if (id === 'revolver') {
    by = .022; adsZ = -.08;
    cz('Metal', .0095, .0095, .13, 0, .022, -.085, 12); bx('Metal', .011, .012, .125, 0, .037, -.082); bx('Metal', .008, .012, .09, 0, .006, -.066); cz('Dark', .0055, .0055, .01, 0, .022, -.147, 8);
    bx('Metal', .024, .054, .075, 0, .012, .012); cz('Metal', .0215, .0215, .046, 0, .014, -.002, 6); cz('Dark', .0222, .0222, .004, 0, .014, -.002, 6); bx('Metal', .009, .022, .014, 0, .048, .05, -.5);
    bx('Wood', .027, .095, .042, 0, -.055, .052, .3); bx('Metal', .006, .004, .05, 0, -.034, .002); bx('Metal', .006, .024, .004, 0, -.022, -.022); bx('Metal', .004, .016, .005, 0, -.022, .006, -.3);
    bx('Metal', .004, .012, .006, 0, .05, -.138); bx('Metal', .012, .008, .008, 0, .046, .04);
    muzzleZ = -.15; sightY = .055; grip = [0, -.055, .052];
  } else {
    const d = GUNDEF[id], rl = d.rl, zf = -rl / 2, zb = rl / 2, hz = zf - d.hg / 2, bl = d.hg + d.brl;
    bx('Metal', .044, .048, rl, 0, .012, 0); bx('Metal', .04, .036, rl * .78, 0, -.028, rl * .08);
    bx('Dark', .002, .016, .05, .0225, .016, -.02); bx('Metal', .028, .008, .02, 0, .03, zb - .005); bx('Metal', .006, .01, .012, .024, .004, .02);
    bx('Steel', .0015, .01, .04, .0235, .017, -.016); bx('Steel', .012, .007, .016, .03, .02, .012); bx('Steel', .003, .006, .02, -.0232, -.004, zb - .05, .5); bx('Steel', .004, .008, .008, .0232, -.012, zf + .06);   // bolt, charging handle, selector, magazine release
    for (const pz of [zf + .03, zb - .04]) add('Steel', new THREE.CylinderGeometry(.0035, .0035, .0465, 8), M(0, -.012, pz, 0, 0, Math.PI / 2));   // takedown pins
    bx('Metal', .01, .028, .004, 0, -.043, zb - .118); bx('Dark', .0455, .003, rl * .5, 0, -.009, 0); add('Steel', new THREE.TorusGeometry(.007, .0018, 5, 10), M(.024, -.012, zb - .012, 0, Math.PI / 2, 0));   // trigger guard, receiver seam, sling loop
    if (!d.pump) { bx('Metal', .02, .007, rl, 0, .0395, 0); for (let i = 0; i < Math.floor(rl / .012); i++) bx('Metal', .022, .004, .006, 0, .045, zf + .006 + i * .012); }
    bx('Metal', .01, .004, .065, 0, -.056, zb - .085); bx('Metal', .004, .02, .006, 0, -.044, zb - .085, -.3);
    if (d.stock === 'wood' && !d.pg) grip = [0, -.045, zb + .03]; else { bx(d.hgWood ? 'Wood' : 'Poly', .03, .095, .04, 0, -.088, zb - .035, .33); grip = [0, -.088, zb - .035]; }
    cz('Metal', d.brlR, d.brlR, bl, 0, by, zf - bl / 2, 12); muzzleZ = zf - bl;
    if (d.dbl) for (const s of [-1, 1]) { cz('Metal', d.brlR, d.brlR, bl, s * .0118, by + .002, zf - bl / 2, 12); cz('Dark', d.brlR * .7, d.brlR * .7, .01, s * .0118, by + .002, muzzleZ + .004, 8); } cz('Dark', d.brlR * .6, d.brlR * .6, .01, 0, by, muzzleZ + .004, 8);
    if (d.pump) {
      cz('Metal', .011, .011, d.hg + .1, 0, -.014, hz - .05); cz('Wood', .025, .025, .14, 0, -.012, hz - .02, 12);
      for (let i = 0; i < 6; i++) bx('Dark', .051, .03, .003, 0, -.014, hz - .075 + i * .022);
      bx('Metal', .008, .006, bl, 0, .036, zf - bl / 2); sp('Metal', .004, 0, .043, muzzleZ + .015); sightY = .05; fore = [0, -.037, hz - .02];
    } else {
      cz(d.hgWood ? 'Wood' : 'Poly', d.hgR, d.hgR * .94, d.hg, 0, by, hz, 8); bx('Metal', .018, .007, d.hg, 0, by + d.hgR + .001, hz);
      for (let i = 0; i < 5; i++) for (const sd of [-1, 1]) bx('Dark', .003, .007, d.hg * .11, sd * d.hgR * .93, by + d.hgR * .25, hz - d.hg * .36 + i * d.hg * .18);   // cooling slots
      cz('Metal', d.brlR + .0045, d.brlR + .0045, .022, 0, by, zf - d.hg - .014, 10); bx('Metal', .006, .016, .012, 0, by - d.brlR - .008, zf - d.hg - .014);   // gas block
      for (let i = 0; i < 3; i++) bx('Dark', d.hgR * 2 + .003, .008, .035, 0, by, hz - d.hg * .3 + i * d.hg * .3);
      cz('Metal', .019, .019, .014, 0, by, zf - .007, 12); cz('Metal', d.brlR + .0055, d.brlR + .0045, .05, 0, by, muzzleZ + .025, 10);
      for (let i = 0; i < 3; i++) bx('Dark', d.brlR * 2 + .012, .005, .006, 0, by, muzzleZ + .012 + i * .013);
      fore = [0, by - d.hgR, hz];
    }
    if (d.optic === 'iron') { const fz = zf - d.hg + .03; bx('Metal', .004, .022, .004, 0, .059, fz); bx('Metal', .016, .014, .016, 0, .047, fz); bx('Metal', .003, .02, .012, .008, .058, fz); bx('Metal', .003, .02, .012, -.008, .058, fz);
      bx('Metal', .024, .01, .012, 0, .047, zb - .03); bx('Metal', .006, .02, .008, .009, .058, zb - .03); bx('Metal', .006, .02, .008, -.009, .058, zb - .03); sightY = .064; }
    if (d.optic === 'scope') { const sy = .078; cz('Metal', .017, .017, .2, 0, sy, -.01, 16, true); cz('Metal', .019, .025, .055, 0, sy, -.135, 16, true); cz('Metal', .022, .018, .045, 0, sy, .11, 16, true);
      add('Metal', new THREE.CylinderGeometry(.009, .009, .022, 10), M(0, sy + .024, -.01)); add('Metal', new THREE.CylinderGeometry(.009, .009, .022, 10), M(.024, sy, -.01, 0, 0, Math.PI / 2));
      bx('Metal', .02, .034, .014, 0, .058, .045); bx('Metal', .02, .034, .014, 0, .058, -.065); cz('Glass', .024, .024, .002, 0, sy, -.16, 16); sightY = sy; adsZ = .2; }
    const mz = d.magZ === 2 ? zb - .035 : d.magZ ? zb + .06 : zf + .055;
    if (d.mag) bx('Metal', .034, .03, .062, 0, -.05, mz);
    if (d.mag === 'curved') { bx('Metal', .026, .09, .052, 0, -.09, mz, .1); bx('Metal', .026, .08, .05, 0, -.165, mz - .016, .3); }
    if (d.mag === 'straight') bx('Metal', .026, .1, .06, 0, -.095, mz, .05);
    if (d.mag === 'stick') bx('Metal', .022, .19, .032, 0, -.14, mz, .04);
    if (d.mag === 'box') { bx('Metal', .085, .1, .11, 0, -.105, mz + .01); bx('Dark', .087, .012, .112, 0, -.062, mz + .01); bx('Metal', .05, .012, .1, 0, .046, -.03); }
    const sl = d.stockL;
    if (d.stock === 'tube') { cz('Metal', .012, .012, sl, 0, by, zb + sl / 2); bx('Poly', .03, .07, .05, 0, -.002, zb + sl - .025); bx('Dark', .032, .09, .012, 0, -.008, zb + sl + .004); }
    if (d.stock === 'solid') { cz('Metal', .014, .014, sl * .6, 0, by, zb + sl * .3); bx('Poly', .034, .07, sl * .7, 0, -.005, zb + sl * .62, -.06); bx('Dark', .036, .105, .014, 0, -.02, zb + sl + .004); }
    if (d.stock === 'wood') { bx('Wood', .036, .05, sl * .5, 0, -.02, zb + sl * .22, -.25); bx('Wood', .038, .085, sl * .6, 0, -.05, zb + sl * .68, -.12); bx('Dark', .04, .1, .012, 0, -.062, zb + sl + .002); }
    if (d.bipod) for (const s of [-1, 1]) seg('Metal', .005, .005, [s * .018, by - .02, muzzleZ + .1], [s * .03, by - .04, muzzleZ + .32], 6);
    if (d.carry) { const fz = zf - d.hg + .03; bx('Metal', .012, .012, rl * .62, 0, .08, .01); bx('Metal', .012, .036, .014, 0, .058, rl * .3); bx('Metal', .012, .036, .014, 0, .058, -rl * .26);
      bx('Metal', .004, .012, .006, .007, .092, rl * .28); bx('Metal', .004, .012, .006, -.007, .092, rl * .28); bx('Metal', .004, .05, .004, 0, .072, fz); sightY = .094; }
    if (d.bolt) { seg('Metal', .0045, .0045, [.022, .02, .07], [.05, -.004, .082], 6); sp('Metal', .009, .052, -.006, .084); }
  }
  if (withArms) {
    const gx = grip[0], gy = grip[1], gz = grip[2];
    sp('Glove', .03, .014, gy, gz + .01, 1, 1.5, 1.15);
    for (let i = 0; i < 4; i++) seg('Glove', .0095, .0085, [.024, gy + .032 - i * .02, gz - .008], [-.02, gy + .032 - i * .02, gz - .03], 8);
    seg('Glove', .011, .009, [.02, gy + .05, gz + .012], [-.018, gy + .055, gz - .012], 8); bx('Glove', .014, .07, .03, .036, gy + .002, gz);
    const Wr = [.024, gy - .03, gz + .05]; seg('Glove', .034, .036, [.018, gy - .012, gz + .03], Wr, 12); seg('Sleeve', .036, .046, Wr, [.12, gy - .16, gz + .42], 14); seg('Sleeve', .042, .042, Wr, [Wr[0] + .007, Wr[1] - .009, Wr[2] + .028], 14);
    if (fore) { const fy = fore[1], fz = fore[2];
      sp('Glove', .032, -.004, fy - .014, fz, 1.15, .75, 1.8);
      for (let i = 0; i < 4; i++) seg('Glove', .0095, .0085, [.012, fy - .016, fz - .036 + i * .021], [.031, fy + .03, fz - .036 + i * .021], 8);
      seg('Glove', .011, .009, [-.026, fy - .008, fz - .02], [-.031, fy + .034, fz - .04], 8);
      const Wl = [-.026, fy - .03, fz + .05]; seg('Glove', .034, .036, [-.01, fy - .02, fz + .03], Wl, 12); seg('Sleeve', .036, .046, Wl, [-.22, fy - .15, fz + .36], 14); seg('Sleeve', .042, .042, Wl, [Wl[0] - .012, Wl[1] - .008, Wl[2] + .024], 14);
    } else {
      sp('Glove', .03, -.016, gy - .012, gz + .004, 1.1, 1.4, 1.2);
      for (let i = 0; i < 4; i++) seg('Glove', .0095, .0085, [-.03, gy + .02 - i * .02, gz - .004], [.012, gy + .02 - i * .02, gz - .036], 8);
      seg('Glove', .011, .009, [-.03, gy + .04, gz + .01], [-.016, gy + .062, gz - .03], 8);
      const Wl = [-.04, gy - .035, gz + .04]; seg('Glove', .034, .036, [-.024, gy - .02, gz + .02], Wl, 12); seg('Sleeve', .036, .046, Wl, [-.2, gy - .17, gz + .36], 14); seg('Sleeve', .042, .042, Wl, [Wl[0] - .012, Wl[1] - .009, Wl[2] + .024], 14);
    }
  }
  const g = new THREE.Group();
  for (const k in P) { const m = new THREE.Mesh(merged(P[k]), MAT['g' + k]); m.castShadow = !withArms; g.add(m); }
  g.userData.muzzleZ = muzzleZ; g.userData.muzzleY = by; g.userData.adsY = -sightY; g.userData.adsZ = adsZ;
  return g;
}
function buildWeaponScene() {
  wscene = new THREE.Scene(); wcam = new THREE.PerspectiveCamera(50, innerWidth / innerHeight, .01, 5);
  // small studio-style reflection map so gun metal reads as metal
  const envS = new THREE.Scene(); envS.add(new THREE.Mesh(new THREE.SphereGeometry(5, 16, 8), new THREE.MeshBasicMaterial({ color: 0x0b0d11, side: THREE.BackSide })));
  const pan = (c, x, y, z, s) => { const m = new THREE.Mesh(new THREE.PlaneGeometry(s, s), new THREE.MeshBasicMaterial({ color: c, side: THREE.DoubleSide })); m.position.set(x, y, z); m.lookAt(0, 0, 0); envS.add(m); };
  pan(0xfff0d0, 2, 3, 1, 2.2); pan(0x4a628c, -3, 1, -2, 3); pan(0x2a2822, 0, -3, 0, 4);
  try { const pm = new THREE.PMREMGenerator(renderer); wscene.environment = pm.fromScene(envS, .03).texture; pm.dispose(); } catch (e) {}
  wscene.add(new THREE.AmbientLight(0x8898b0, .35));
  wLight = new THREE.PointLight(0xfff0d8, 1.4, 3); wLight.position.set(.1, .25, -.1); wscene.add(wLight);
  gunRoot = new THREE.Group(); wscene.add(gunRoot);
  for (const id in WEAPONS) { const m = buildGun(id, true); m.visible = false; gunRoot.add(m); gunViews[id] = m; }
  const ft = canvasTex(128, (g, s) => { g.translate(s / 2, s / 2); for (let i = 0; i < 9; i++) { g.rotate(Math.PI * 2 / 9 + rnd(-.2, .2)); const len = rnd(28, 62), gr = g.createLinearGradient(0, 0, len, 0);
    gr.addColorStop(0, 'rgba(255,240,190,1)'); gr.addColorStop(1, 'rgba(255,130,20,0)'); g.fillStyle = gr; g.beginPath(); g.moveTo(0, -7); g.lineTo(len, 0); g.lineTo(0, 7); g.fill(); } });
  muzzleFlash = new THREE.Mesh(new THREE.PlaneGeometry(.22, .22), new THREE.MeshBasicMaterial({ map: ft, transparent: true, blending: THREE.AdditiveBlending, depthWrite: false }));
  muzzleFlash.visible = false; gunRoot.add(muzzleFlash);
  knife = buildKnife(); knife.visible = false; wscene.add(knife);
}
function buildKnife() {
  const P = {}, add = (k, geo, m) => { (P[k] = P[k] || []).push([geo, m]); };
  const bx = (k, w, h, l, x, y, z, rx, ry, rz) => add(k, new THREE.BoxGeometry(w, h, l), M(x, y, z, rx, ry, rz));
  const seg = (k, rA, rB, A, B, n) => { const a = V3(A[0], A[1], A[2]), b = V3(B[0], B[1], B[2]), d = b.clone().sub(a), len = d.length();
    const q = new THREE.Quaternion().setFromUnitVectors(V3(0, 1, 0), d.normalize()); add(k, new THREE.CylinderGeometry(rB, rA, len, n || 10), new THREE.Matrix4().compose(a.add(b).multiplyScalar(.5), q, V3(1, 1, 1))); };
  // blade points forward (-Z), edge down
  bx('Metal', .0045, .036, .15, 0, .012, -.115); add('Metal', q4(.0002, .0255, .055), M(0, .012, -.2175, -Math.PI / 2, 0, 0, .125, 1, 1));
  bx('Dark', .005, .005, .1, 0, .018, -.11); for (let i = 0; i < 6; i++) bx('Dark', .0052, .008, .006, 0, .029, -.06 - i * .012);
  bx('Metal', .014, .064, .012, 0, .008, -.036); bx('Metal', .02, .034, .014, 0, .006, .09);
  add('Poly', new THREE.CylinderGeometry(.0155, .0165, .115, 10), M(0, .006, .027, Math.PI / 2, 0, 0, .8, 1, 1.25));
  for (let i = 0; i < 5; i++) bx('Dark', .0265, .042, .004, 0, .006, -.012 + i * .02);
  // gloved fist around the handle, forearm running back and down to the right
  add('Glove', new THREE.SphereGeometry(.03, 10, 8), M(.006, -.004, .03, 0, 0, 0, 1.05, 1.35, 1.55));
  for (let i = 0; i < 4; i++) seg('Glove', .0098, .0088, [-.02, .03, -.004 + i * .021], [-.018, -.024, -.002 + i * .021], 8);
  seg('Glove', .011, .009, [.012, .03, .03], [-.006, .034, -.016], 8);
  const Wr = [.02, -.03, .075]; seg('Glove', .033, .035, [.008, -.012, .05], Wr, 12); seg('Sleeve', .036, .048, Wr, [.16, -.2, .46], 14); seg('Sleeve', .043, .043, Wr, [Wr[0] + .008, Wr[1] - .01, Wr[2] + .03], 14);
  const g = new THREE.Group(); for (const k in P) g.add(new THREE.Mesh(merged(P[k]), MAT['g' + k])); return g;
}

// ---------------------------------------------------------------- particles / decals
const PN = 500, pPos = new Float32Array(PN * 3), pCol = new Float32Array(PN * 3), pVel = new Float32Array(PN * 3), pLife = new Float32Array(PN); let pIdx = 0, pGeo;
const holes = [], bloods = []; let holeI = 0, bloodI = 0, dust;
function buildFX() {
  pGeo = new THREE.BufferGeometry(); for (let i = 0; i < PN; i++) pPos[i * 3 + 1] = -999;
  pGeo.setAttribute('position', new THREE.BufferAttribute(pPos, 3)); pGeo.setAttribute('color', new THREE.BufferAttribute(pCol, 3));
  const pts = new THREE.Points(pGeo, new THREE.PointsMaterial({ size: .07, vertexColors: true, transparent: true, depthWrite: false })); pts.frustumCulled = false; scene.add(pts);
  const hm = new THREE.MeshBasicMaterial({ color: 0x050505, polygonOffset: true, polygonOffsetFactor: -4, transparent: true, opacity: .85 });
  for (let i = 0; i < 50; i++) { const m = new THREE.Mesh(new THREE.CircleGeometry(.045, 8), hm); m.visible = false; scene.add(m); holes.push(m); }
  const bt = canvasTex(128, (g, s) => { g.clearRect(0, 0, s, s); for (let i = 0; i < 16; i++) { const x = s / 2 + rnd(-30, 30), y = s / 2 + rnd(-30, 30), r = rnd(8, 30), gr = g.createRadialGradient(x, y, 0, x, y, r);
    gr.addColorStop(0, 'rgba(70,3,3,.95)'); gr.addColorStop(.7, 'rgba(50,2,2,.8)'); gr.addColorStop(1, 'rgba(40,0,0,0)'); g.fillStyle = gr; g.fillRect(x - r, y - r, r * 2, r * 2); } });
  const bm = new THREE.MeshStandardMaterial({ map: bt, transparent: true, depthWrite: false, roughness: .25, polygonOffset: true, polygonOffsetFactor: -3 });
  const bg = new THREE.PlaneGeometry(1.5, 1.5); bg.rotateX(-Math.PI / 2);
  for (let i = 0; i < 36; i++) { const m = new THREE.Mesh(bg, bm); m.visible = false; scene.add(m); bloods.push(m); }
  const dg = new THREE.BufferGeometry(), dp = new Float32Array(240 * 3); for (let i = 0; i < dp.length; i++) dp[i] = rnd(-6, 6);
  dg.setAttribute('position', new THREE.BufferAttribute(dp, 3));
  dust = new THREE.Points(dg, new THREE.PointsMaterial({ size: .022, color: 0x8a8a80, transparent: true, opacity: .3, depthWrite: false })); dust.frustumCulled = false; scene.add(dust);
}
const tracers = [], cases = []; let trI = 0, caI = 0, lastTink = 0;
function buildShots() {
  const tm = new THREE.MeshBasicMaterial({ color: 0xffd9a0, transparent: true, opacity: .55, blending: THREE.AdditiveBlending, depthWrite: false }), tg = new THREE.BoxGeometry(.012, .012, 1);
  for (let i = 0; i < 10; i++) { const m = new THREE.Mesh(tg, tm); m.visible = false; m.frustumCulled = false; scene.add(m); tracers.push({ m, t: 0 }); }
  const cm = new THREE.MeshStandardMaterial({ color: 0xb08a3a, metalness: .9, roughness: .35 }), cg = new THREE.CylinderGeometry(.006, .006, .024, 6);
  for (let i = 0; i < 24; i++) { const m = new THREE.Mesh(cg, cm); m.visible = false; scene.add(m); cases.push({ m, t: 0, v: new THREE.Vector3(), g: 0, b: 0 }); }
}
function tracer(to) {   // a streak from the muzzle to wherever the round went
  const T = tracers[trI = (trI + 1) % tracers.length], m = T.m; camera.getWorldDirection(_q3); _v2.copy(camera.position).addScaledVector(_q3, .9); _q3.cross(_up).normalize(); _v2.addScaledVector(_q3, .17 * (1 - L.ads)); _v2.y -= .13 * (1 - L.ads) + .04;
  const len = _v2.distanceTo(to); if (len < 2) return; m.position.copy(_v2).lerp(to, .5); m.lookAt(to); m.scale.set(1, 1, len); m.visible = true; T.t = .05;
}
function casing() {   // spent brass thrown out to the right
  const C = cases[caI = (caI + 1) % cases.length], m = C.m; camera.getWorldDirection(_q3); _v2.copy(camera.position).addScaledVector(_q3, .45); const fx = _q3.x, fz = _q3.z; _q3.cross(_up).normalize(); _v2.addScaledVector(_q3, .2); _v2.y -= .12;
  m.position.copy(_v2); C.v.copy(_q3).multiplyScalar(rnd(1.6, 2.6)); C.v.y = rnd(1.4, 2.4); C.v.x += fx * rnd(-.4, .4) + L.vx; C.v.z += fz * rnd(-.4, .4) + L.vz; C.t = 2.5; C.g = me.y + .012; C.b = 0; m.rotation.set(rnd(0, 6), rnd(0, 6), rnd(0, 6)); m.visible = true;
}
function updateShots(dt) {
  for (const T of tracers) if (T.t > 0) { T.t -= dt; if (T.t <= 0) T.m.visible = false; }
  for (const C of cases) { if (C.t <= 0) continue; C.t -= dt; if (C.t <= 0) { C.m.visible = false; continue; } if (C.b > 1) continue; C.v.y -= 9.8 * dt; C.m.position.addScaledVector(C.v, dt); C.m.rotation.x += dt * 14; C.m.rotation.z += dt * 9;
    if (C.m.position.y <= C.g) { C.m.position.y = C.g; C.b++; C.v.y *= -.35; C.v.x *= .5; C.v.z *= .5; if (C.b > 1) C.m.rotation.set(Math.PI / 2, 0, rnd(0, 6)); else if (AC && AC.currentTime - lastTink > .09) { lastTink = AC.currentTime; sTone(rnd(3200, 4600), .05, .035, 'sine'); } } }
}
function burst(pos, n, col, speed, dir) {
  for (let k = 0; k < n; k++) { const i = pIdx = (pIdx + 1) % PN;
    pPos[i * 3] = pos.x; pPos[i * 3 + 1] = pos.y; pPos[i * 3 + 2] = pos.z;
    pVel[i * 3] = rnd(-1, 1) * speed + (dir ? dir.x * speed : 0); pVel[i * 3 + 1] = rnd(-.3, 1.2) * speed + (dir ? dir.y * speed : 0); pVel[i * 3 + 2] = rnd(-1, 1) * speed + (dir ? dir.z * speed : 0);
    const b = rnd(.6, 1); pCol[i * 3] = col[0] * b; pCol[i * 3 + 1] = col[1] * b; pCol[i * 3 + 2] = col[2] * b; pLife[i] = rnd(.3, .8); }
}
function updateFX(dt) {
  for (let i = 0; i < PN; i++) { if (pLife[i] <= 0) continue; pLife[i] -= dt; pVel[i * 3 + 1] -= 9 * dt;
    pPos[i * 3] += pVel[i * 3] * dt; pPos[i * 3 + 1] += pVel[i * 3 + 1] * dt; pPos[i * 3 + 2] += pVel[i * 3 + 2] * dt;
    if (pLife[i] <= 0 || pPos[i * 3 + 1] < 0) { pLife[i] = 0; pPos[i * 3 + 1] = -999; } }
  pGeo.attributes.position.needsUpdate = true; pGeo.attributes.color.needsUpdate = true;
  dust.position.set(Math.round(camera.position.x / 12) * 12, 1.8 + Math.sin(G.time * .2) * .3, Math.round(camera.position.z / 12) * 12);
  dust.rotation.y = G.time * .01;
  updateLights(dt); cullChunks(); updateShots(dt);
  { const cur = OBJ.list[G.oi] || {}, bl = Math.sin(G.time * 7) > 0;
    OBJ.gens.forEach((t, i) => t.lamp.material.color.setHex((G.og >> i) & 1 ? 0x30ff50 : bl ? 0xff2010 : 0x400804));
    OBJ.sups.forEach((t, i) => { t.m.visible = cur.t === 'sup' && !((G.om >> i) & 1); t.m.rotation.y += dt * .8; }); if (OBJ.zone) OBJ.zone.m.visible = cur.t === 'hold'; }
}
function bloodDecal(x, z, y) { const m = bloods[bloodI = (bloodI + 1) % bloods.length]; m.position.set(x, (y || 0) + .015 + bloodI * .0004, z); m.rotation.y = rnd(0, 6); const s = rnd(.6, 1.3); m.scale.set(s, 1, s); m.visible = true; }

// ---------------------------------------------------------------- players
function newPlayer(id, name) {
  return { id, name: name || 'Survivor', x: SPAWN.x + rnd(-1.5, 1.5), y: 0, z: SPAWN.z + rnd(-1.5, 1.5), yaw: 0, pitch: 0, hp: 100, maxHp: 100, down: false,
    points: 500, kills: 0, wid: 'pistol', fireSeq: 0, lastHurt: -99, view: null, ci: 0, l: 0, sk: 0 };
}
function removePlayer(id) { const p = players[id]; if (!p) return; if (p.view) scene.remove(p.view.g); delete players[id]; }
const curW = () => L.weapons[L.wi];
function giveWeapon(id) {
  const d = WEAPONS[id], w = { id, ammo: d.mag, reserve: d.reserve };
  if (L.weapons.length < 2) { L.weapons.push(w); L.wi = L.weapons.length - 1; } else L.weapons[L.wi] = w;
  L.switchT = .4; L.reloadT = 0; me.wid = id;
}
function switchWeapon(i) { if (i === L.wi || !L.weapons[i] || me.down) return; L.wi = i; L.switchT = .35; L.reloadT = 0; L.burstN = 0; me.wid = curW().id; sNoise(2000, .05, .15); }
function startReload() { const w = curW(), d = WEAPONS[w.id]; if (L.reloadT > 0 || w.ammo >= magOf(w) || w.reserve <= 0) return; L.reloadT = d.reload; sNoise(2500, .06, .25); setTimeout(() => sNoise(1800, .08, .3), d.reload * 700); }

const _v = new THREE.Vector3(), _d = new THREE.Vector3(), _q = new THREE.Quaternion(), _v2 = new THREE.Vector3(), _q3 = new THREE.Vector3();
function castShot(dir, far) {
  raycaster.set(camera.position, dir); raycaster.far = far;
  const hits = raycaster.intersectObjects(shootables, true);
  for (const h of hits) { const z = h.object.userData.zr; if (z && (z.dead || z.rise < .5)) continue; return h; }
  return null;
}
// how far shots can stray right now: tight when still and aiming, wider when moving or holding the trigger down
function spreadNow(d, moving) {
  if (d.pellets > 1) return d.spread * (1 - L.ads * .35);
  return (d.spread * (.45 + L.bloom * .55) + (1 - L.ads) * .0025) * (1 - L.ads * .85) * (moving ? 1.3 : 1) * (L.onGround ? 1 : 1.6) * (1 - L.crouch * .3);
}
function fire() {
  const w = curW(), d = WEAPONS[w.id]; w.ammo--; L.fireT = 60 / d.rpm; L.fired = true; L.kick = 1;
  const moving = keys.KeyW || keys.KeyA || keys.KeyS || keys.KeyD;
  const sp = spreadNow(d, moving); L.bloom = Math.min(1, L.bloom + (d.auto ? .16 : .3));
  let anyHit = false, anyHead = false;
  for (let i = 0; i < d.pellets; i++) {
    camera.getWorldDirection(_d); _d.x += rnd(-sp, sp); _d.y += rnd(-sp, sp); _d.z += rnd(-sp, sp); _d.normalize();
    const h = castShot(_d, 120); if (i < 4) tracer(h ? h.point : _v.copy(camera.position).addScaledVector(_d, 70)); if (!h) continue;
    const z = h.object.userData.zr;
    if (d.splash) {   // explosive round: everything near the impact is hit, less the further out it is
      burst(h.point, 46, [1, .55, .15], 5); burst(h.point, 22, [.3, .3, .3], 2.5); sNoise(110, .7, 1); sTone(60, .5, .8, 'sine', 0, 30); muzzleLight.intensity = 5;
      for (const q of zombies) { if (q.dead) continue; const dd = Math.hypot(q.x - h.point.x, q.z - h.point.z, ((q.y || 0) + 1) - h.point.y); if (dd < d.splash) { anyHit = true; dealHit(q.id, dmgOf(w) * (1 - dd / d.splash * .65), false); } }
      continue; }
    if (z) { const head = !!h.object.userData.head; anyHit = true; if (head) anyHead = true; burst(h.point, head ? 14 : 8, [.4, .02, .02], 1.8); dealHit(z.id, dmgOf(w) * (head ? 2.5 : 1), head); }
    else { burst(h.point, 5, [.5, .45, .35], 1.4);
      if (h.face) { const m = holes[holeI = (holeI + 1) % holes.length]; _v.copy(h.face.normal); if (h.object.rotation.y) _v.applyEuler(h.object.rotation);
        m.position.copy(h.point).addScaledVector(_v, .012); m.lookAt(_v.add(m.position)); m.visible = true; } }
  }
  if (anyHit) { L.hitFx = 1; sFlesh(anyHead); }
  if (w.id !== 'revolver' && w.id !== 'dbl' && w.id !== 'launcher') casing();
  me.pitch = Math.min(1.5, me.pitch + d.kick * (1 - L.ads * .4)); me.yaw += rnd(-1, 1) * d.kick * .2;
  me.fireSeq++; sShot(d.snd || w.id, 1);
  muzzleLight.intensity = 3.2; muzzleFlash.visible = true; muzzleFlash.rotation.z = rnd(0, 6); muzzleFlash.scale.setScalar(rnd(.8, 1.4) * (d.pellets > 1 ? 1.6 : 1));
  setTimeout(() => { muzzleLight.intensity = 0; muzzleFlash.visible = false; }, 45);
  if (w.ammo === 0 && w.reserve > 0) setTimeout(startReload, 250);
}
const KNIFE_T = .48, _up = new THREE.Vector3(0, 1, 0);
function melee() {
  if (L.meleeT > 0 || !me || me.down || L.switchT > 0) return; L.meleeT = KNIFE_T; L.meleeHit = true; sNoise(1500, .1, .28, 'bandpass'); sNoise(700, .16, .18, 'highpass');
}
function knifeHit() {   // the slash lands part-way through the swing and covers a small arc
  for (const a of [0, -.2, .2, -.4, .4]) { camera.getWorldDirection(_d); if (a) _d.applyAxisAngle(_up, a); const h = castShot(_d, 2.7);
    if (h && h.object.userData.zr) { burst(h.point, 16, [.4, .02, .02], 2.2); dealHit(h.object.userData.zr.id, 160, false, true); L.hitFx = 1; sNoise(200, .12, .6); sNoise(1300, .14, .4, 'bandpass'); sTone(90, .1, .4, 'sine', 0, 50); return; } }
}
function dealHit(zid, dmg, head, knife) { if (G.host) hostHit(G.myId, zid, dmg, head, knife); else netSend({ t: 'hit', z: zid, d: Math.round(dmg), h: head ? 1 : 0, k: knife ? 1 : 0 }); }

// ---------------------------------------------------------------- interaction
function nearestInteractable() {
  if (!me || me.down) return null; let best = null, bd = 1e9;
  for (const it of interactables) { if ((it.type === 'door' && doorOpen[it.id]) || (it.type === 'abox' && it.ref.taken) || (it.l || 0) !== (me.l || 0)) continue; const d = Math.hypot(it.x - me.x, it.z - me.z); if (d < it.range && d < bd) { bd = d; best = it; } }
  return best;
}
function promptFor(it) {
  if (it.type === 'door') return `Press <b>E</b> to clear the barricade to ${DOORS[it.id].name} &nbsp;[${it.cost}]`;
  if (it.type === 'crate') return L.crateT > 0 ? '' : `Press <b>E</b> to open the Mystery Crate — random weapon &nbsp;[${it.cost}]`;
  if (it.type === 'ammo') return `Press <b>E</b> to restock ammo &nbsp;[${it.cost}]`;
  if (it.type === 'abox') return 'Press <b>E</b> to take the ammo';
  if (it.type === 'wbuy') return owns(it.id) ? `Press <b>E</b> for ${WEAPONS[it.id].name} ammo &nbsp;[${it.cost / 2}]` : `Press <b>E</b> to buy the ${WEAPONS[it.id].name} &nbsp;[${it.cost}]`;
  if (it.type === 'up') return curW().up ? 'This weapon is already upgraded' : `Press <b>E</b> to upgrade your ${WEAPONS[curW().id].name} — more damage, bigger magazine &nbsp;[${it.cost}]`;
  if (it.type === 'gen') return (G.og >> it.id) & 1 ? 'Generator running' : 'Press <b>E</b> to start the generator — the noise will draw them';
  if (it.type === 'evac') return G.evacT > 0 ? 'Extraction inbound — hold the roof' : G.round < EVAC_WAVE ? `Extraction unlocks at wave ${EVAC_WAVE}` : `Press <b>E</b> to call extraction — then hold the roof for ${EVAC_TIME} seconds`;
  return me.maxHp > 100 ? 'Field Stim already taken' : `Press <b>E</b> for Field Stim — double health &nbsp;[${it.cost}]`;
}
const owns = id => L.weapons.some(w => w.id === id);
function takeAmmoBox(b) {
  let got = 0; L.weapons.forEach((w, i) => { const n = Math.min(resOf(w) - w.reserve, magOf(w) * (i === L.wi ? 2 : 1)); if (n > 0) { w.reserve += n; got += n; } });
  if (!got) { showMsg('AMMO ALREADY FULL', 1.2); return; }
  b.taken = true; b.g.visible = false; showMsg('AMMO +' + got, 1.2); sNoise(2600, .05, .3); sTone(700, .08, .18, 'triangle', .05);
}
function requestBuy(it) {
  if (it.type === 'abox') { if (!it.ref.taken) takeAmmoBox(it.ref); return; }
  if (it.type === 'up' && curW().up) return;
  if (it.type === 'wbuy' && owns(it.id) && me.points >= it.cost / 2) { const m = { t: 'buy', k: 'wbuy', i: it.id, own: L.weapons.map(w => w.id) }; if (G.host) hostBuy(G.myId, m); else netSend(m); return; }
  if (it.type === 'crate' && L.crateT > 0) return;
  if (it.type === 'stim' && me.maxHp > 100) return;
  if (it.type === 'evac' && (G.round < EVAC_WAVE || G.evacT > 0)) return;
  if (it.type === 'gen') { if ((G.og >> it.id) & 1) return; sNoise(90, 1.4, .6); sTone(55, 1.6, .4, 'sawtooth', 0, 80); }
  if (me.points < it.cost) { sTone(140, .18, .25, 'square'); return; }
  if (it.type === 'crate') L.crateRef = it.ref;
  const m = { t: 'buy', k: it.type, i: it.id === undefined ? '' : it.id, own: L.weapons.map(w => w.id) };
  if (G.host) hostBuy(G.myId, m); else netSend(m);
}
function hostBuy(pid, m) {
  const p = players[pid]; if (!p || p.down) return; let w = null;
  if (m.k === 'door') { const d = DOORS[m.i]; if (!d || doorOpen[m.i] || p.points < d.cost) return; p.points -= d.cost; openDoor(m.i); }
  else if (m.k === 'crate') { if (p.points < COST.crate) return; p.points -= COST.crate; const own = m.own || []; const pool = Object.keys(WEAPONS).filter(k => k !== 'pistol' && own.indexOf(k) < 0); w = pool[(Math.random() * pool.length) | 0]; }
  else if (m.k === 'ammo') { if (p.points < COST.ammo) return; p.points -= COST.ammo; }
  else if (m.k === 'wbuy') { const c = WCOST[m.i]; if (!c) return; const price = (m.own || []).indexOf(m.i) >= 0 ? c / 2 : c; if (p.points < price) return; p.points -= price; w = m.i; }
  else if (m.k === 'up') { if (p.points < UP_COST) return; p.points -= UP_COST; }
  else if (m.k === 'stim') { if (p.points < COST.stim || p.maxHp > 100) return; p.points -= COST.stim; p.maxHp = 200; p.hp = 200; }
  else if (m.k === 'gen') { const cur = OBJ.list[G.oi], i = m.i | 0; if (!cur || cur.t !== 'gen' || !OBJ.gens[i] || (G.og >> i) & 1) return; G.og |= 1 << i; p.points += 250; G.toSpawn += 4; hostSay('GENERATOR ' + bits(G.og) + '/' + cur.n + ' RUNNING'); return; }
  else if (m.k === 'evac') { if (!EVAC || G.round < EVAC_WAVE || G.evacT > 0) return; G.evacT = EVAC_TIME; G.toSpawn += 20; hostSay('EXTRACTION INBOUND — HOLD THE ROOF'); return; }
  else return;
  const ok = { t: 'ok', k: m.k, i: m.i, w };
  if (pid === G.myId) onBuyOk(ok); else if (Net.conns[pid]) Net.conns[pid].send(ok);
}
function onBuyOk(m) {
  sTone(660, .1, .2, 'triangle'); sTone(990, .16, .2, 'triangle', .09);
  if (m.k === 'crate') { L.crateT = 3.4; L.crateW = m.w; [392, 494, 587, 784, 587, 784, 988].forEach((f, i) => sTone(f, .22, .12, 'triangle', .2 + i * .38)); }
  else if (m.k === 'ammo') { for (const w of L.weapons) { w.reserve = resOf(w); } showMsg('AMMO RESTOCKED', 1.5); }
  else if (m.k === 'wbuy') { const o = L.weapons.find(w => w.id === m.w); if (o) { o.reserve = resOf(o); o.ammo = magOf(o); showMsg(wName(o).toUpperCase() + ' AMMO', 1.5); } else { giveWeapon(m.w); showMsg(WEAPONS[m.w].name.toUpperCase(), 2); } sNoise(2200, .08, .3); }
  else if (m.k === 'up') { const w = curW(); w.up = 1; w.ammo = magOf(w); w.reserve = resOf(w); L.reloadT = 0; showMsg(wName(w).toUpperCase() + ' — UPGRADED', 2.5); sNoise(900, .5, .5); [330, 440, 660, 880].forEach((f, i) => sTone(f, .3, .15, 'sawtooth', i * .12)); }
  else if (m.k === 'stim') showMsg('FIELD STIM', 1.5);
}
function onEvent(k) {
  if (k === 'ammo') { for (const w of L.weapons) { w.reserve = resOf(w); w.ammo = magOf(w); } showMsg('RESUPPLY', 2); }
  if (k === 'insta') showMsg('OVERKILL', 2);
  if (k === 'nuke') { showMsg('PURGE', 2); sNoise(120, 1.4, 1); }
  if (k === 'pick') { sTone(520, .15, .2, 'triangle'); sTone(780, .25, .2, 'triangle', .1); }
}
function broadcast(m) { for (const id in Net.conns) { try { Net.conns[id].send(m); } catch (e) {} } }
function hostEvent(k) { onEvent(k); broadcast({ t: 'ev', k }); }
function hostSay(s) { showMsg(s, 2.5); broadcast({ t: 'msg', s }); }
function dropClient(id) { const c = Net.conns[id], p = players[id]; if (c) { delete Net.conns[id]; try { c.close(); } catch (e) {} } if (p && id !== G.myId) { hostSay(p.name.toUpperCase() + ' LEFT'); removePlayer(id); flowT = 0; } }

// ---------------------------------------------------------------- host simulation
const ZTYPES = {
  walker:  { hp: 1,   sp: 1,   dmg: 34, pts: 0,   from: 1, w: 10,  wg: 0,   cap: 10 },
  runner:  { hp: .6,  sp: 1.8, dmg: 26, pts: 20,  from: 2, w: 1.5, wg: .9,  cap: 6 },
  crawler: { hp: .7,  sp: .85, dmg: 28, pts: 20,  from: 3, w: 1.2, wg: .5,  cap: 4 },
  armored: { hp: 1.5, sp: .9,  dmg: 38, pts: 50,  from: 4, w: 1,   wg: .6,  cap: 5 },
  bloater: { hp: 1.2, sp: .75, dmg: 30, pts: 60,  from: 5, w: .8,  wg: .45, cap: 3 },
  brute:   { hp: 5,   sp: .72, dmg: 60, pts: 200, from: 6, w: .4,  wg: .3,  cap: 2.5 }
}, ZT = Object.keys(ZTYPES);
function pickType(r) {   // each type unlocks at its wave and then gets steadily more common
  let tot = 0; const ws = ZT.map(k => { const t = ZTYPES[k], w = r < t.from ? 0 : Math.min(t.w + (r - t.from) * t.wg, t.cap); tot += w; return w; });
  let x = Math.random() * tot; for (let i = 0; i < ZT.length; i++) { x -= ws[i]; if (x < 0) return ZT[i]; } return 'walker';
}
function buildFlow() {
  flow.fill(9999); const q = [], WH = W * H;
  for (const id in players) { const p = players[id]; if (p.down) continue; const l = p.l || 0, c = Math.floor(p.x / TILE), r = Math.floor(p.z / TILE); if (solidL(l, c, r)) continue; const i = nidx(l, c, r); if (flow[i] !== 0) { flow[i] = 0; q.push(i); } }
  for (let h = 0; h < q.length; h++) { const i = q[h], l = (i / WH) | 0, rem = i - l * WH, c = rem % W, r = (rem / W) | 0, d = flow[i] + 1;
    for (const [dc, dr] of N4) { const nl = navStep(l, c, r, dc, dr); if (nl < 0) continue; const ni = nidx(nl, c + dc, r + dr); if (flow[ni] > d) { flow[ni] = d; q.push(ni); } } }
}
const N8 = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
function ambush(p) {   // one claws its way out of the floor right behind somebody
  const l = p.l || 0, c = Math.floor(p.x / TILE), r = Math.floor(p.z / TILE), bx = Math.round(Math.sin(p.yaw)), bz = Math.round(Math.cos(p.yaw));
  if (NL > 1 && STAIR[tileL(l, c, r)]) return false;
  for (const [dc, dr] of [[bx, bz], [bx * 2, bz * 2], [bz, -bx], [-bz, bx]]) { if (!dc && !dr) continue; const cc = c + dc, rr = r + dr;
    if (navSolidL(l, cc, rr) || !(flow[nidx(l, cc, rr)] < 9000) || (Math.abs(dc) === 2 || Math.abs(dr) === 2) && navSolidL(l, c + dc / 2, r + dr / 2)) continue;
    return spawnZombie(null, { x: wx(cc), z: wx(rr), l, c: cc, r: rr }); }
  return false;
}
function spawnZombie(force, at) {
  const fd = s => flow[nidx(s.l || 0, s.c, s.r)], ok = zSpawns.filter(s => fd(s) < 9000); if (!ok.length) return false;
  let far = ok.filter(s => fd(s) >= 3 && fd(s) <= 13); if (!far.length) far = ok.filter(s => fd(s) >= 3); if (!far.length) far = ok;
  const s = at || far[(Math.random() * far.length) | 0], r = G.round, type = ZTYPES[force] ? force : pickType(r), T = ZTYPES[type];
  const z = { id: zSeq++, type, l: s.l || 0, x: s.x + (at ? 0 : rnd(-1, 1)), z: s.z + (at ? 0 : rnd(-1, 1)), y: (s.l || 0) * FH, rot: rnd(0, 6), rise: at ? .45 : 0, atk: 0, atkT: .5, dead: false,
    hp: (r < 10 ? 100 + (r - 1) * 55 : 595 * Math.pow(1.1, r - 9)) * T.hp, speed: Math.min(6.6, (1.5 + Math.min(r, 12) * .16 + Math.random() * .5) * T.sp) };
  zombies.push(z); zById[z.id] = z; makeZombieView(z); return true;
}
function killZombie(z, head, silent) {
  const i = zombies.indexOf(z); if (i >= 0) zombies.splice(i, 1); delete zById[z.id]; z.dead = true;
  const v = z.view, y = z.y || 0; if (!v) return;
  if (head) { v.head.traverse(o => { if (o.isMesh) o.visible = false; }); _v.set(z.x, y + 1.6, z.z); burst(_v, 26, [.4, .02, .02], 2.6); }
  if (z.type === 'bloater' && !silent) {   // bursts when it dies: keep your distance
    const vol = distVol(z.x, z.z, 40); _v.set(z.x, y + 1, z.z); burst(_v, 70, [.3, .5, .08], 4.5); sNoise(160, .5, vol * 1.2); sTone(70, .35, vol * .7, 'sine', 0, 30);
    if (G.host) for (const id in players) { const p = players[id]; if (Math.hypot(p.x - z.x, p.z - z.z) < 3.8 && Math.abs(p.y - y) < 2.5) damagePlayer(p, 45); } }
  bloodDecal(z.x, z.z, y); corpses.push({ v, t: 0 });
  if (!silent) { const vol = distVol(z.x, z.z, 26), pn = panOf(z.x, z.z); if (head) sCrack(vol); (Math.random() < .5 ? sGurgle : sGroan)(vol * .8, pn); }
}
function hostHit(pid, zid, dmg, head, knife) {
  const z = zById[zid], p = players[pid]; if (!z || !p) return; const T = ZTYPES[z.type] || ZTYPES.walker;
  if (z.type === 'armored' && !head && !knife) dmg *= .35;
  z.hp -= G.insta > 0 ? 1e9 : dmg; p.points += 10;
  if (z.hp <= 0) {
    p.points += (knife ? 120 : head ? 90 : 50) + T.pts; p.kills++;
    if (drops.length < 2 && Math.random() < .045) drops.push({ id: dropSeq++, type: ['ammo', 'insta', 'nuke'][(Math.random() * 3) | 0], x: z.x, z: z.z, y: z.y || 0, t: 25 });
    killZombie(z, head);
  }
}
function damagePlayer(p, d) { if (p.down) return; p.hp -= d; p.lastHurt = G.time; if (p.hp <= 0) { p.hp = 0; p.down = true; flowT = 0; } }
function startRound() {
  G.round++; G.state = 'wave'; const n = Object.keys(players).length;
  G.toSpawn = Math.round((5 + G.round * 2.6) * (1 + .55 * (n - 1))); G.spawnT = 1.5;
  for (const id in players) { const p = players[id]; if (p.down) { p.down = false; p.hp = p.maxHp; } }
}
const bits = v => { let n = 0; while (v) { n += v & 1; v >>= 1; } return n; };
function objDone(cur) { G.oi++; G.op = 0; for (const id in players) players[id].points += 750; hostSay('OBJECTIVE COMPLETE  +750'); hostEvent('pick'); }
function objUpdate(dt, alive) {
  const cur = OBJ.list[G.oi]; if (!cur) return; const at = (p, t, r) => (p.l || 0) === t.l && Math.hypot(p.x - t.x, p.z - t.z) < r;
  if (cur.t === 'gen') { if (bits(G.og) >= cur.n) objDone(cur); }
  else if (cur.t === 'sup') { OBJ.sups.forEach((t, i) => { if ((G.om >> i) & 1) return; const p = alive.find(q => at(q, t, 1.6)); if (!p) return; G.om |= 1 << i; p.points += 300;
      const ok = { t: 'ok', k: 'ammo' }; if (p.id === G.myId) onBuyOk(ok); else if (Net.conns[p.id]) Net.conns[p.id].send(ok); hostSay('SUPPLY CASE ' + bits(G.om) + '/' + cur.n); });
    if (bits(G.om) >= cur.n) objDone(cur); }
  else if (cur.t === 'hold') { if (alive.some(p => at(p, OBJ.zone, 5))) { G.op += dt; if (G.toSpawn < 6 && G.state === 'wave') G.toSpawn = 6; } if (G.op >= cur.n) objDone(cur); }
}
function objText() {   // HUD line: what to do, how far along, and which way to go
  const cur = OBJ.list[G.oi]; if (!cur) return OBJ.list.length ? 'All objectives complete — survive' : '';
  let prog = '', tg = null; const nearest = (arr, mask) => { let b = null, bd = 1e9; arr.forEach((t, i) => { if ((mask >> i) & 1) return; const d = Math.hypot(t.x - me.x, t.z - me.z) + Math.abs(t.l - (me.l || 0)) * 30; if (d < bd) { bd = d; b = t; } }); return b; };
  if (cur.t === 'gen') { prog = bits(G.og) + '/' + cur.n; tg = nearest(OBJ.gens, G.og); }
  else if (cur.t === 'sup') { prog = bits(G.om) + '/' + cur.n; tg = nearest(OBJ.sups, G.om); }
  else if (cur.t === 'hold') { prog = Math.floor(G.op) + '/' + cur.n + 's'; tg = OBJ.zone; }
  else if (cur.t === 'evac') { if (G.evacT > 0) return ''; prog = G.round < EVAC_WAVE ? 'unlocks at wave ' + EVAC_WAVE : 'ready'; tg = EVAC; }
  let way = '';
  if (tg) { const dx = tg.x - me.x, dz = tg.z - me.z, f = -dx * Math.sin(me.yaw) - dz * Math.cos(me.yaw), r = dx * Math.cos(me.yaw) - dz * Math.sin(me.yaw);
    way = ' &nbsp;<b>' + ['↑', '↗', '→', '↘', '↓', '↙', '←', '↖'][(Math.round(Math.atan2(r, f) / (Math.PI / 4)) + 8) % 8] + ' ' + Math.round(Math.hypot(dx, dz)) + 'm</b>' + (tg.l > (me.l || 0) ? ' ▲ upstairs' : tg.l < (me.l || 0) ? ' ▼ downstairs' : ''); }
  return 'Objective ' + (G.oi + 1) + '/' + OBJ.list.length + ': ' + cur.title + ' (' + prog + ')' + way;
}
function hostUpdate(dt) {
  if (G.over) return;
  flowT -= dt; if (flowT <= 0) { flowT = .25; buildFlow(); }
  const all = Object.values(players), alive = all.filter(p => !p.down);
  if (all.length && !alive.length) { G.over = true; G.state = 'over'; sendSnapshot(); gameOver(); return; }
  if (G.insta > 0) G.insta -= dt;
  objUpdate(dt, alive);
  if (G.evacT > 0) {   // extraction called: hold the roof until the timer runs out
    G.evacT -= dt; if (G.toSpawn < 8) G.toSpawn = 8; if (G.state === 'inter') { G.state = 'wave'; G.spawnT = .5; }
    if (G.evacT <= 0) { G.evacT = 0;
      if (EVAC && alive.some(p => (p.l || 0) === EVAC.l && Math.hypot(p.x - EVAC.x, p.z - EVAC.z) < 9)) { G.over = true; G.state = 'won'; sendSnapshot(); gameOver(true); return; }
      hostSay('THE CHOPPER LEFT WITHOUT YOU'); } }
  if (G.state === 'inter') { G.interT -= dt; if (G.interT <= 0) startRound(); }
  else {
    G.spawnT -= dt;
    if (G.toSpawn > 0 && G.spawnT <= 0 && zombies.length < MAX_ALIVE + 5 * (all.length - 1)) { if (spawnZombie()) G.toSpawn--; G.spawnT = Math.max(.35, 2 - G.round * .12) * (G.evacT > 0 ? .5 : 1); }
    G.ambT = (G.ambT === undefined ? rnd(25, 45) : G.ambT) - dt;
    if (G.ambT <= 0) { G.ambT = rnd(28, 65); if (G.round >= 2 && G.toSpawn > 0 && alive.length && ambush(alive[(Math.random() * alive.length) | 0])) G.toSpawn--; }
    if (G.toSpawn <= 0 && !zombies.length) { G.state = 'inter'; G.interT = 9; }
  }
  for (const z of zombies) {
    if (z.rise < 1) { z.rise = Math.min(1, z.rise + dt / 1.5); continue; }
    const T = ZTYPES[z.type] || ZTYPES.walker, zy = z.y || 0;
    let tp = null, td = 1e9; for (const p of alive) { const d = Math.hypot(p.x - z.x, p.z - z.z) + Math.max(0, Math.abs(p.y - zy) - 1.2) * 3; if (d < td) { td = d; tp = p; } }
    if (!tp) continue;
    let gx = tp.x, gz = tp.z; const l = z.l || 0, c = Math.floor(z.x / TILE), r = Math.floor(z.z / TILE), here = flow[nidx(l, c, r)];
    if (here > 1 && here < 9000) { let best = here, bc = c, br = r; const onStair = NL > 1 && STAIR[tileL(l, c, r)] === 1;
      for (const [dc, dr] of N8) { let nl = l;
        if (dc && dr) { if (onStair || navSolidL(l, c + dc, r + dr) || navSolidL(l, c + dc, r) || navSolidL(l, c, r + dr)) continue; }
        else { nl = navStep(l, c, r, dc, dr); if (nl < 0) continue; }
        const d = flow[nidx(nl, c + dc, r + dr)] + (dc && dr ? .4 : 0); if (d < best) { best = d; bc = c + dc; br = r + dr; } }
      gx = wx(bc); gz = wx(br); }
    let dx = gx - z.x, dz = gz - z.z; const dl = Math.hypot(dx, dz) || 1; dx /= dl; dz /= dl;
    z.rot = lerpAngle(z.rot, Math.atan2(td < 2.5 ? tp.x - z.x : dx, td < 2.5 ? tp.z - z.z : dz), dt * 8);
    for (const o of zombies) { if (o === z || Math.abs((o.y || 0) - zy) > 2) continue; const ox = z.x - o.x, oz = z.z - o.z, d2 = ox * ox + oz * oz; if (d2 < .5 && d2 > 1e-4) { const d = Math.sqrt(d2); dx += ox / d * (.72 - d) * 2.5; dz += oz / d * (.72 - d) * 2.5; } }
    const lunge = td < 6 && z.type !== 'brute' && z.type !== 'crawler' ? 1.3 : 1;   // they speed up for the last few steps
    let mul = lunge;   // walkers sometimes stop dead, twitch, then rush you
    if (z.type === 'walker' || z.type === 'armored') { z.dc = (z.dc === undefined ? rnd(3, 10) : z.dc) - dt; if (z.dc <= 0) { z.dc = rnd(7, 16); if (td > 4 && td < 15) { z.fz = .6; z.bo = 1.5; } }
      if (z.fz > 0) { z.fz -= dt; mul = 0; } else if (z.bo > 0) { z.bo -= dt; mul = Math.max(lunge, Math.min(2.4, 6.2 / z.speed)); } }
    if (td > .9 && mul) moveCollide(z, z.x + dx * z.speed * mul * dt, z.z + dz * z.speed * mul * dt, .32);
    z.y = groundY(z);
    z.atkT -= dt; if (z.atk > 0) z.atk -= dt;
    if (td < (z.type === 'brute' ? 1.7 : 1.3) && z.atkT <= 0) { z.atkT = z.type === 'brute' ? 1.5 : 1.1; z.atk = .45; damagePlayer(tp, T.dmg); }
  }
  for (const p of all) if (!p.down && p.hp < p.maxHp && G.time - p.lastHurt > 5) p.hp = Math.min(p.maxHp, p.hp + 30 * dt);
  for (let i = drops.length - 1; i >= 0; i--) { const d = drops[i]; d.t -= dt; let got = false;
    for (const p of alive) if (Math.hypot(p.x - d.x, p.z - d.z) < 1.2 && Math.abs(p.y - (d.y || 0)) < 2.5) got = true;
    if (got) { hostEvent('pick'); if (d.type === 'insta') G.insta = 20;
      if (d.type === 'nuke') { for (const z of zombies.slice()) killZombie(z, false, true); for (const p of all) p.points += 400; }
      hostEvent(d.type); }
    if (got || d.t <= 0) drops.splice(i, 1); }
  Net.sendT -= dt; if (Net.sendT <= 0) { Net.sendT = 1 / 14; sendSnapshot(); const now = performance.now(); for (const id in Net.conns) if (now - (Net.conns[id].seen || now) > 12000) dropClient(id); }
}
const r2 = v => Math.round(v * 100) / 100;
function sendSnapshot() {
  if (!Object.keys(Net.conns).length) return;
  broadcast({ t: 's', r: G.round, st: G.state, it: r2(G.interT), left: G.toSpawn + zombies.length, insta: r2(Math.max(0, G.insta)), ev: r2(G.evacT || 0), o: [G.oi, r2(G.op), G.og, G.om], doors: Object.keys(doorOpen).join(''),
    P: Object.values(players).map(p => [p.id, p.name, r2(p.x), r2(p.y), r2(p.z), r2(p.yaw), r2(p.pitch), Math.round(p.hp), p.maxHp, p.down ? 1 : 0, p.points, p.kills, p.wid, p.fireSeq, p.ci | 0, p.l | 0, p.sk | 0]),
    Z: zombies.map(z => [z.id, r2(z.x), r2(z.z), r2(z.rot), r2(z.rise), z.atk > 0 ? 1 : 0, r2(z.y || 0), ZT.indexOf(z.type)]), D: drops.map(d => [d.id, d.type, r2(d.x), r2(d.z), r2(d.y || 0)]) });
}
function hostRecv(pid, m) {
  if (!m || !m.t) return;
  if (m.t === 'hello') { const c = Net.conns[pid];
    if (!players[pid]) {
      if (Object.keys(players).length >= 4 || G.over) { if (c) { try { c.send({ t: 'full' }); } catch (e) {} setTimeout(() => { try { c.close(); } catch (e) {} }, 600); } delete Net.conns[pid]; return; }
      const p = players[pid] = newPlayer(pid, String(m.name || 'Survivor').slice(0, 14)); p.sk = clamp(m.sk | 0, 0, SKINS.length - 1);
      p.ci = [1, 2, 3, 0].find(i => !Object.values(players).some(q => q !== p && q.ci === i)) || 0; hostSay(p.name.toUpperCase() + ' JOINED'); }
    if (c) c.send({ t: 'w', map: MAPID, doors: Object.keys(doorOpen).join('') }); return; }
  const p = players[pid]; if (!p) return;
  if (m.t === 'p') { p.x = +m.a[0] || 0; p.y = +m.a[1] || 0; p.z = +m.a[2] || 0; p.yaw = +m.a[3] || 0; p.pitch = +m.a[4] || 0; if (WEAPONS[m.a[5]]) p.wid = m.a[5]; p.fireSeq = m.a[6] | 0; p.l = Math.max(0, Math.min(NL - 1, m.a[7] | 0)); }
  else if (m.t === 'hit') hostHit(pid, m.z, Math.min(2500, +m.d || 0), !!m.h, !!m.k);
  else if (m.t === 'buy') hostBuy(pid, m);
}

// ---------------------------------------------------------------- client
function clientRecv(m) {
  if (!m || !m.t) return;
  if (m.t === 'ok') return onBuyOk(m);
  if (m.t === 'ev') return onEvent(m.k);
  if (m.t === 'msg') return showMsg(String(m.s).slice(0, 40), 2.5);
  if (m.t !== 's') return;
  G.round = m.r; G.state = m.st; G.interT = m.it; G.left = m.left; G.insta = m.insta; G.evacT = m.ev || 0; if (m.o) { G.oi = m.o[0] | 0; G.op = +m.o[1] || 0; G.og = m.o[2] | 0; G.om = m.o[3] | 0; }
  for (const ch of m.doors) if (!doorOpen[ch]) openDoor(ch);
  const seenP = {};
  for (const a of m.P) { const id = a[0]; seenP[id] = 1; let p = players[id]; if (!p) { p = players[id] = newPlayer(id, a[1]); }
    p.name = a[1]; p.ci = a[14] | 0; if (id !== G.myId && p.sk !== (a[16] | 0)) { p.sk = a[16] | 0; if (p.view) { scene.remove(p.view.g); p.view = null; } } p.hp = a[7]; p.maxHp = a[8]; p.down = !!a[9]; p.points = a[10]; p.kills = a[11];
    if (id !== G.myId) { p.x = a[2]; p.y = a[3]; p.z = a[4]; p.yaw = a[5]; p.pitch = a[6]; p.wid = a[12]; p.fireSeq = a[13]; p.l = a[15] | 0; } }
  for (const id in players) if (!seenP[id] && id !== G.myId) removePlayer(id);
  const seenZ = {};
  for (const a of m.Z) { let z = zById[a[0]]; seenZ[a[0]] = 1;
    if (!z) { z = { id: a[0], type: ZT[a[7]] || 'walker', x: a[1], z: a[2], y: a[6] || 0, rot: a[3], rise: a[4], atk: 0, dead: false }; zombies.push(z); zById[z.id] = z; makeZombieView(z); }
    z.x = a[1]; z.z = a[2]; z.y = a[6] || 0; z.rot = a[3]; z.rise = a[4]; z.atk = a[5] ? .3 : 0; }
  for (const z of zombies.slice()) if (!seenZ[z.id]) killZombie(z, false);
  drops.length = 0; for (const a of m.D) drops.push({ id: a[0], type: a[1], x: a[2], z: a[3], y: a[4] || 0 });
  if ((m.st === 'over' || m.st === 'won') && !G.over) { G.over = true; gameOver(m.st === 'won'); }
}
function netSend(m) { if (Net.conn && Net.conn.open) Net.conn.send(m); }
function hostLost() {
  if (G.over) return; G.over = true; document.exitPointerLock && document.exitPointerLock();
  $('overtitle').textContent = 'DISCONNECTED'; $('overtext').textContent = 'The connection to the host was lost.'; $('over').style.display = 'flex';
}
function clientUpdate(dt) {
  if (Net.lastRecv && performance.now() - Net.lastRecv > 9000) hostLost();
  Net.sendT -= dt; if (Net.sendT <= 0) { Net.sendT = 1 / 15; netSend({ t: 'p', a: [r2(me.x), r2(me.y), r2(me.z), r2(me.yaw), r2(me.pitch), me.wid, me.fireSeq, me.l | 0] }); }
}

// ---------------------------------------------------------------- local player
function updateLocal(dt) {
  if (me.hp < L.lastHp - .5) { L.hurt = 1; sHurt(); } L.lastHp = me.hp;
  gunRoot.visible = !me.down;
  if (me.down) { L.wasDown = true; L.vx = L.vz = 0; const mate = Object.values(players).find(p => p !== me && !p.down); L.spec = mate ? mate.name : null;   // dead until the next wave: watch a team-mate
    if (mate) { camera.position.set(mate.x + Math.sin(mate.yaw) * 2.4, mate.y + 2.4, mate.z + Math.cos(mate.yaw) * 2.4); camera.rotation.set(-.28, mate.yaw, 0); }
    else { camera.position.set(me.x, me.y + .4, me.z); camera.rotation.set(-.2, me.yaw, .5); } return; }
  if (L.wasDown) { L.wasDown = false; me.x = SPAWN.x; me.z = SPAWN.z; me.l = 0; L.jy = 0; for (const w of L.weapons) w.ammo = magOf(w); showMsg('BACK ON YOUR FEET', 2); }
  const f = (keys.KeyW ? 1 : 0) - (keys.KeyS ? 1 : 0), s = (keys.KeyD ? 1 : 0) - (keys.KeyA ? 1 : 0), cr = !!keys.KeyC;
  L.crouch += ((cr ? 1 : 0) - L.crouch) * Math.min(1, dt * 10);
  if (L.stam <= 0) L.winded = true; else if (L.stam > .35) L.winded = false;
  L.sprint = !!(keys.ShiftLeft || keys.ShiftRight) && f > 0 && !mouse.r && !cr && !L.winded;
  if (L.sprint) { L.stam = Math.max(0, L.stam - dt / 8); L.stamT = .9; } else { L.stamT -= dt; if (L.stamT <= 0) L.stam = Math.min(1, L.stam + dt / 4.5); }
  if (L.stam < .3) { L.brT -= dt; if (L.brT <= 0) { L.brT = 1.1; sBreath(.1 + (.3 - L.stam) * .4); } }
  const sp = mouse.r ? 2.4 : cr ? 2.1 : L.sprint ? 6.5 : 4.1, len = Math.hypot(f, s) || 1, sin = Math.sin(me.yaw), cos = Math.cos(me.yaw);
  const acc = Math.min(1, dt * (L.onGround ? (f || s ? 12 : 10) : 2.5));   // you build up and lose speed instead of starting and stopping instantly
  L.vx += ((-sin * f + cos * s) / len * sp - L.vx) * acc; L.vz += ((-cos * f - sin * s) / len * sp - L.vz) * acc;
  const px = me.x, pz = me.z; moveCollide(me, me.x + L.vx * dt, me.z + L.vz * dt, .38);
  if (dt > 0) { if (Math.abs(me.x - px) < Math.abs(L.vx * dt) * .5) L.vx *= .5; if (Math.abs(me.z - pz) < Math.abs(L.vz * dt) * .5) L.vz *= .5; }   // lose speed against walls
  if (keys.Space && L.onGround && L.crouch < .5) { L.vy = 5.2; L.onGround = false; sNoise(200, .06, .12); }
  L.vy -= 14 * dt; L.jy += L.vy * dt;
  if (L.jy <= 0) { if (!L.onGround && L.vy < -2) { L.land = Math.min(1, -L.vy / 7); sNoise(120, .12, .3 * L.land); sTone(60, .12, .35 * L.land, 'sine', 0, 35); } L.jy = 0; L.vy = 0; L.onGround = true; }
  L.land = Math.max(0, L.land - dt * 5); L.roll += (-s * .016 * (1 - L.ads) - L.roll) * Math.min(1, dt * 8); L.swx *= Math.exp(-dt * 10); L.swy *= Math.exp(-dt * 10);
  me.y = groundY(me) + L.jy;
  const spd = Math.hypot(L.vx, L.vz), moving = spd > .7 && L.onGround;
  if (moving) { L.bob += dt * (2.2 + spd * 1.7); if (Math.floor(L.bob / Math.PI) !== L.stepPh) { L.stepPh = Math.floor(L.bob / Math.PI); const sv = cr ? .05 : L.sprint ? .24 : .14; sNoise(rnd(120, 170), .07, sv); sTone(rnd(62, 78), .07, sv * .9, 'sine', 0, 40); if (L.sprint) sNoise(900, .04, sv * .3, 'highpass'); } }
  // weapon
  const w = curW(), d = WEAPONS[w.id]; L.fireT -= dt; if (L.switchT > 0) L.switchT -= dt; if (L.meleeT > 0) { L.meleeT -= dt; if (L.meleeHit && L.meleeT < KNIFE_T * .62) { L.meleeHit = false; knifeHit(); } }
  if (L.reloadT > 0) { L.reloadT -= dt; if (L.reloadT <= 0) { const n = Math.min(magOf(w) - w.ammo, w.reserve); w.ammo += n; w.reserve -= n; } }
  if (mouse.l && document.pointerLockElement && L.fireT <= 0 && L.reloadT <= 0 && L.switchT <= 0 && L.meleeT <= 0 && !L.burstN && (d.auto || !L.fired)) {
    if (w.ammo > 0) { fire(); if (d.burst) L.burstN = d.burst - 1; } else { L.fired = true; sTone(900, .03, .15, 'square'); startReload(); } }
  if (L.burstN > 0 && L.fireT <= 0) { if (w.ammo > 0 && L.reloadT <= 0 && L.switchT <= 0) { fire(); if (!--L.burstN) L.fireT = .2; } else L.burstN = 0; }
  if (!mouse.l) L.fired = false;
  const wantAds = mouse.r && L.reloadT <= 0 && !L.sprint ? 1 : 0; L.ads += (wantAds - L.ads) * Math.min(1, dt * 14);
  L.kick = Math.max(0, L.kick - dt * 9); L.bloom = Math.max(0, L.bloom - dt * 2.6); L.hitFx = Math.max(0, L.hitFx - dt * 5); L.hurt = Math.max(0, L.hurt - dt * 1.2);
  // crate animation
  if (L.crateT > 0) { L.crateT -= dt; const c = L.crateRef || crateObj, k = 3.4 - L.crateT; c.lidP.rotation.x = -Math.min(1, k * 3) * 1.3; c.glow.base = 1.7;
    const ids = Object.keys(c.models), showId = L.crateT < .9 ? L.crateW : ids[Math.floor(k * 8) % ids.length];
    for (const id of ids) c.models[id].visible = id === showId; c.show.position.set(c.x, c.y + 1 + Math.min(.5, k * .4), c.z); c.show.rotation.y += dt * 1.5;
    if (L.crateT <= 0) { for (const id of ids) c.models[id].visible = false; c.lidP.rotation.x = 0; c.glow.base = .8; giveWeapon(L.crateW); showMsg(WEAPONS[L.crateW].name.toUpperCase(), 2); sNoise(2200, .08, .3); } }
  // camera
  const bobY = moving ? Math.sin(L.bob * 2) * (L.sprint ? .055 : .03) * (1 - L.ads * .7) : 0;
  camera.position.set(me.x, EYE - L.crouch * .62 - L.land * .11 + me.y + bobY, me.z); camera.rotation.set(me.pitch + (L.hurt > .45 ? rnd(-.035, .035) : 0), me.yaw + (L.hurt > .45 ? rnd(-.035, .035) : 0), (moving ? Math.sin(L.bob) * .006 : 0) + (L.hurt > .3 ? rnd(-.05, .05) * L.hurt : 0));
  camera.rotation.z += L.roll; if (L.shake > 0) { camera.rotation.x += rnd(-1, 1) * L.shake * .02; camera.rotation.z += rnd(-1, 1) * L.shake * .025; }
  const fov = 72 / (1 + (d.zoom - 1) * L.ads) + (L.sprint ? 4 : 0); if (Math.abs(camera.fov - fov) > .05) { camera.fov += (fov - camera.fov) * Math.min(1, dt * 12); camera.updateProjectionMatrix(); }
  // view model
  for (const id in gunViews) gunViews[id].visible = id === w.id;
  const gv = gunViews[w.id], a = L.ads, rl = L.reloadT > 0 ? Math.sin((1 - L.reloadT / d.reload) * Math.PI) : 0, sw = Math.max(0, L.switchT) / .4, ml = L.meleeT > 0 ? Math.sin((1 - L.meleeT / KNIFE_T) * Math.PI) : 0;
  const sprintK = L.sprint && moving ? 1 : 0;
  gunRoot.position.set(.165 * (1 - a) + Math.cos(L.bob) * .008 * (1 - a) * (moving ? 1 : 0) - sprintK * .05,
    -.135 * (1 - a) + gv.userData.adsY * a + (moving ? Math.abs(Math.sin(L.bob)) * .01 * (1 - a) : 0) - rl * .16 - sw * .3 - sprintK * .06 + Math.sin(G.time * 1.6) * .002,
    -.5 + (gv.userData.adsZ + .08) * a + L.kick * .05 + ml * .04);
  gunRoot.position.x -= ml * .1; gunRoot.position.y -= ml * .12;
  gunRoot.rotation.set(L.kick * .09 - rl * .8 + sprintK * -.25 - ml * .25, sprintK * .6 + ml * .45, rl * .3 + ml * .25);
  gunRoot.rotation.y += clamp(L.swx * .0007, -.07, .07) * (1 - a * .7); gunRoot.rotation.x += clamp(L.swy * .0007, -.05, .05) * (1 - a * .7); gunRoot.position.y -= L.land * .03; gunRoot.rotation.z += L.roll * 1.5;
  knife.visible = L.meleeT > 0;
  if (knife.visible) { const t = 1 - L.meleeT / KNIFE_T, e = t * t * (3 - 2 * t), sw = Math.sin(t * Math.PI);
    knife.position.set(.3 - .56 * e, -.03 - .13 * e + .06 * sw, -.36 - .13 * sw); knife.rotation.set(.45 - .7 * e, .15 + 1.15 * e, -.7 + 1.3 * e); }
  muzzleFlash.position.set(0, gv.userData.muzzleY, gv.userData.muzzleZ - .06);
  // the torch falters when something is close, and during a blackout
  const fear = L.nearZ < 6 ? .3 + (6 - L.nearZ) * .15 : blackT > 0 ? 1.6 : .2; if (Math.random() < fear * dt) L.flick = rnd(.04, .13);   // flickers per second
  if (L.flick > 0) L.flick -= dt; flashlight.intensity = L.flash ? 2.9 * (L.flick > 0 ? rnd(.05, .5) : 1) : 0; wLight.intensity = L.flash ? 1.4 : .4;
}

// ---------------------------------------------------------------- views
const dropMeshes = {};
function updateViews(dt) {
  const k = Math.min(1, dt * 12); L.nearZ = 99;
  for (const z of zombies) { const v = z.view, g = v.g; const ox = g.position.x, oz = g.position.z;
    g.position.x += (z.x - ox) * k; g.position.z += (z.z - oz) * k; v.gy += ((z.y || 0) - v.gy) * k; g.position.y = v.gy + (Math.min(1, z.rise) - 1) * 1.9;
    g.rotation.y = lerpAngle(g.rotation.y, z.rot, dt * 10);
    const mv = Math.hypot(g.position.x - ox, g.position.z - oz); v.ph += mv * 3.4; const ph = v.ph, t = G.time + v.tw;
    v.legs[0].rotation.x = Math.sin(ph) * .65; v.legs[1].rotation.x = -Math.sin(ph) * (v.limp ? .25 : .65);
    v.shins[0].rotation.x = Math.max(0, -Math.sin(ph)) * .9 + .1; v.shins[1].rotation.x = Math.max(0, Math.sin(ph)) * .9 + .1;
    const atk = z.atk > 0 ? Math.sin(z.atk / .45 * Math.PI) : 0; const rising = z.rise < 1 ? 1 : 0;
    for (let i = 0; i < 2; i++) { v.arms[i].rotation.x = v.armDown === i ? -.2 + Math.sin(ph) * .3 : -1.35 + Math.sin(t * 2 + i * 2) * .12 - atk * .7 - rising * 1.2; v.arms[i].rotation.z = (i ? -1 : 1) * (.12 + atk * .2); v.fore[i].rotation.x = -.25 - atk * .5; }
    const dm = Math.hypot(z.x - me.x, z.z - me.z) + Math.abs((z.y || 0) - me.y + L.jy) * 2, pn = panOf(z.x, z.z), close = clamp((7 - dm) / 5, 0, 1); if (dm < L.nearZ) L.nearZ = dm;
    const spz = Math.sin(t * 27) * Math.max(0, Math.sin(t * 1.9 + v.tw * 3) - .8) * 5;   // sudden violent twitches
    v.torso.rotation.x = .38 + Math.sin(ph * 2) * .06 + atk * .3 + close * .12 + spz * .08; v.torso.rotation.z = Math.sin(ph) * .07 + (v.limp ? .12 : 0);
    v.head.rotation.z = Math.sin(t * 2.7) * .2 + spz * .5 + close * Math.sin(t * 31) * .06; v.head.rotation.x = -.28 + Math.sin(t * 1.3) * .1 - close * .15; v.head.rotation.y = spz * .4;
    if (v.jaw) v.jaw.rotation.x = .16 + Math.sin(t * 3.1 + v.tw) * .08 + atk * .75 + close * (.45 + Math.sin(t * 19) * .12) + Math.abs(spz) * .3;
    v.sp += (mv / Math.max(dt, .001) - v.sp) * Math.min(1, dt * 6); const rush = v.run ? 0 : clamp((v.sp - 3.4) / 2.5, 0, 1);
    v.head.rotation.z += v.neck; g.rotation.z = Math.sin(ph) * .05 * (v.run || v.crawl ? .3 : 1) + spz * .03;
    if (dm < 13 && !v.crawl) { let a = Math.atan2(me.x - z.x, me.z - z.z) - g.rotation.y; a = Math.atan2(Math.sin(a), Math.cos(a)); v.head.rotation.y += clamp(a, -1.2, 1.2); }   // the head turns to keep looking at you
    if (v.sp < .4 && z.rise >= 1 && dm > 2.2 && !v.crawl) { v.head.rotation.z += Math.sin(t * 43) * .28; v.torso.rotation.z += Math.sin(t * 37) * .06; for (let i = 0; i < 2; i++) v.arms[i].rotation.x = -.15 + Math.sin(t * 29 + i) * .12; }   // stopped dead, shaking
    if (rush) { v.torso.rotation.x += rush * .42; for (let i = 0; i < 2; i++) { v.arms[i].rotation.x = -1.35 + rush * (2 + Math.sin(ph + i * 3) * .3) - atk * 1.6; v.arms[i].rotation.z = (i ? -1 : 1) * (.12 + rush * .45); } if (v.jaw) v.jaw.rotation.x = Math.max(v.jaw.rotation.x, rush * .9); }
    if (rush > .5 && !v.dsh) { v.dsh = 1; sScream(distVol(z.x, z.z, 24) * .9, pn); } else if (v.sp < 2.5) v.dsh = 0;
    if (z.type === 'brute') { const st = Math.floor(ph / Math.PI); if (st !== v.stp) { v.stp = st; const vv = distVol(z.x, z.z, 24); sStomp(vv); L.shake = Math.max(L.shake, vv * .7); } }
    if (v.run) { v.torso.rotation.x += .32; for (let i = 0; i < 2; i++) { v.arms[i].rotation.x = .5 + Math.sin(ph + i * Math.PI) * .9 - atk * 1.8; v.fore[i].rotation.x = -1.1; } }
    if (v.crawl) { v.body.rotation.x = 1.45; v.body.position.set(0, .12, -.7); v.torso.rotation.x = 0; v.torso.rotation.z = Math.sin(ph * 1.5) * .12; v.head.rotation.x = -1.25;
      for (let i = 0; i < 2; i++) { v.arms[i].rotation.x = -2.75 + Math.sin(ph * 1.5 + i * Math.PI) * .55 - atk * .4; v.fore[i].rotation.x = -.25; } }
    if (!v.spn) { v.spn = 1; if (z.rise < .9) sSpawn(distVol(z.x, z.z, 24), pn); }
    if (z.atk > 0 && !v.lastAtk) sSnarl(distVol(z.x, z.z, 16), pn); v.lastAtk = z.atk > 0 ? 1 : 0;
    if (Math.random() < dt * .2) (v.crawl || Math.random() < .25 ? sHiss : sGroan)(distVol(z.x, z.z, 28) * .75, pn);
    if (dm < 7 && !v.scr && z.rise >= 1) { v.scr = 1; if (Math.random() < .65) sScream(.55 + .35 * (1 - dm / 7), pn);
      const behind = (z.x - me.x) * -Math.sin(me.yaw) + (z.z - me.z) * -Math.cos(me.yaw) < 0; if (behind && dm < 5 && G.time - L.stingT > 14) { L.stingT = G.time; sSting(); } }
    if (dm > 12) v.scr = 0;
  }
  for (let i = corpses.length - 1; i >= 0; i--) { const c = corpses[i]; c.t += dt; const f = Math.min(1, c.t / .5);
    if (!c.v.crawl) { c.v.body.rotation.x = -f * f * Math.PI / 2; c.v.body.position.y = f * .16; c.v.arms[0].rotation.x = c.v.arms[1].rotation.x = -1.35 + f * 1.2; } else c.v.head.rotation.x = -1.25 + f * 1.2;
    if (c.t > 6) c.v.g.position.y -= dt * .25; if (c.t > 8) { zGroup.remove(c.v.g); corpses.splice(i, 1); } }
  for (const id in players) { const p = players[id]; if (id === G.myId) continue; if (!p.view) makePlayerView(p); const v = p.view, g = v.g, ox = g.position.x, oz = g.position.z;
    g.position.x += (p.x - ox) * k; g.position.z += (p.z - oz) * k; g.position.y = p.y; g.rotation.y = lerpAngle(g.rotation.y, p.yaw + Math.PI, dt * 12);
    v.ph += Math.hypot(g.position.x - ox, g.position.z - oz) * 3; v.legs[0].rotation.x = Math.sin(v.ph) * .6; v.legs[1].rotation.x = -Math.sin(v.ph) * .6;
    v.torso.rotation.x = -p.pitch * .5; v.body.rotation.x = p.down ? -Math.PI / 2 : 0; v.body.position.y = p.down ? .2 : 0;
    if (v.seq !== p.fireSeq) { v.seq = p.fireSeq; sShot((WEAPONS[p.wid] || {}).snd || p.wid, distVol(p.x, p.z, 45) * .8); remoteFlash.position.set(p.x - Math.sin(p.yaw) * .8, p.y + 1.4, p.z - Math.cos(p.yaw) * .8); remoteFlash.intensity = 2.5; setTimeout(() => { remoteFlash.intensity = 0; }, 50); } }
  // power-up drops
  const seen = {};
  for (const d of drops) { seen[d.id] = 1; let m = dropMeshes[d.id];
    if (!m) { const col = { ammo: 0x40ff60, insta: 0xff4030, nuke: 0xffd040 }[d.type]; m = new THREE.Mesh(new THREE.OctahedronGeometry(.28), new THREE.MeshBasicMaterial({ color: col }));
      const l = new THREE.PointLight(col, .9, 6, 1.6); m.add(l); scene.add(m); dropMeshes[d.id] = m; }
    m.position.set(d.x, (d.y || 0) + 1 + Math.sin(G.time * 3) * .12, d.z); m.rotation.y = G.time * 2; }
  for (const id in dropMeshes) if (!seen[id]) { scene.remove(dropMeshes[id]); delete dropMeshes[id]; }
  updateScares(dt);
}
// ---------------------------------------------------------------- jump scares
function scareFace() {   // a face, full screen, for a quarter of a second
  const el = $('scare'); if (!el.style.backgroundImage) { const c = document.createElement('canvas'); c.width = c.height = 512; const g = c.getContext('2d');
    const gr = g.createRadialGradient(256, 250, 30, 256, 256, 300); gr.addColorStop(0, '#cfc8b4'); gr.addColorStop(.55, '#8f8672'); gr.addColorStop(.8, '#2a2620'); gr.addColorStop(1, 'rgba(0,0,0,0)'); g.fillStyle = gr; g.beginPath(); g.ellipse(256, 262, 190, 250, 0, 0, 7); g.fill();
    g.fillStyle = '#000'; for (const s of [-1, 1]) { g.beginPath(); g.ellipse(256 + s * 78, 196, 52, 40, s * .25, 0, 7); g.fill(); }
    g.fillStyle = '#e8e0d0'; for (const s of [-1, 1]) { g.beginPath(); g.arc(256 + s * 74, 200, 7, 0, 7); g.fill(); }
    g.fillStyle = '#000'; g.beginPath(); g.moveTo(256, 250); g.lineTo(238, 296); g.lineTo(274, 296); g.fill(); g.beginPath(); g.ellipse(256, 400, 74, 104, 0, 0, 7); g.fill();
    g.fillStyle = '#b8b09a'; for (let i = 0; i < 7; i++) { g.fillRect(200 + i * 17, 318 + Math.abs(i - 3) * 5, 11, 26); g.fillRect(204 + i * 16, 462 - Math.abs(i - 3) * 6, 10, 22); }
    g.strokeStyle = 'rgba(60,0,0,.8)'; g.lineWidth = 5; for (let i = 0; i < 9; i++) { const x = 130 + Math.random() * 250, y = 200 + Math.random() * 120; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-8, 8), y + rnd(60, 190)); g.stroke(); }
    el.style.backgroundImage = 'url(' + c.toDataURL() + ')'; }
  el.style.display = 'block'; el.style.transform = 'scale(' + rnd(1.1, 1.5) + ')'; setTimeout(() => { el.style.transform = 'scale(2.2)'; }, 30); setTimeout(() => { el.style.display = 'none'; }, 260);
}
// a tall dark figure that stands in your light, watches, then comes at you and is gone. It does no damage.
const ghost = { v: null, st: 0, t: 0, seen: 0, next: 45 };
function updateScares(dt) {
  if (!me || !G.started || G.over) return; const gh = ghost;
  if (L.shake > 0) L.shake = Math.max(0, L.shake - dt * 2.5);
  if (!gh.v) { gh.v = buildHumanoid({ skin: MAT.gDark, face: MAT.gDark, cloth: MAT.gDark, pants: MAT.gDark, shoe: MAT.gDark, eye: MAT.eyeR, hair: true }); gh.v.g.scale.set(.82, 1.28, .82); gh.v.g.visible = false; gh.v.g.traverse(o => { o.castShadow = false; }); }
  const g = gh.v.g, v = gh.v; if (g.parent !== scene) scene.add(g);
  if (gh.st === 0) { g.visible = false; if (me.down) return; gh.next -= dt; if (gh.next > 0) return;
    if (L.nearZ < 10) { gh.next = 4; return; }
    const l = me.l || 0, sx = -Math.sin(me.yaw), sz = -Math.cos(me.yaw); let best = 0;
    if (STAIR[tileL(l, Math.floor(me.x / TILE), Math.floor(me.z / TILE))]) { gh.next = 3; return; }
    for (let d = 1; d <= 5; d++) { const c = Math.floor((me.x + sx * d * TILE) / TILE), r = Math.floor((me.z + sz * d * TILE) / TILE), ch = tileL(l, c, r); if (solidL(l, c, r) || STAIR[ch] || ch === 'v' || navBlock[nidx(l, c, r)]) break; best = d; }
    if (best < 3) { gh.next = 3; return; }
    g.position.set(me.x + sx * best * TILE, l * FH, me.z + sz * best * TILE); g.visible = true; gh.st = 1; gh.t = 0; gh.seen = 0; return; }
  const dx = me.x - g.position.x, dz = me.z - g.position.z, dist = Math.hypot(dx, dz) || 1; g.rotation.y = Math.atan2(dx, dz); gh.t += dt;
  if (gh.st === 1) { v.arms[0].rotation.x = v.arms[1].rotation.x = -.05; v.head.rotation.z = .45 + Math.sin(gh.t * 23) * (Math.sin(gh.t * 1.7) > .8 ? .2 : 0); v.torso.rotation.x = .1; if (v.jaw) v.jaw.rotation.x = .1;
    camera.getWorldDirection(_d); if ((-dx * _d.x - dz * _d.z) / dist > .9) gh.seen += dt;
    if (dist < 6 || gh.seen > 1.5) { gh.st = 2; gh.t = 0; sSting(); sScream(1, 0); L.flick = .6; L.shake = 1; }
    else if (gh.t > 22 || Math.abs((me.l || 0) * FH - g.position.y) > .1) { gh.st = 0; gh.next = rnd(30, 60); }
    return; }
  const sp = Math.min(24 * dt, dist); g.position.x += dx / dist * sp; g.position.z += dz / dist * sp;   // it comes straight at you
  v.arms[0].rotation.x = v.arms[1].rotation.x = -1.7; v.torso.rotation.x = .5; v.head.rotation.z = Math.sin(gh.t * 60) * .3; if (v.jaw) v.jaw.rotation.x = 1;
  if (dist < 1.3 || gh.t > .6) { gh.st = 0; gh.next = rnd(55, 120); g.visible = false; L.hurt = Math.max(L.hurt, .7); if (Math.random() < .6) scareFace(); }
}

// ---------------------------------------------------------------- HUD
let lastRound = -1, hudCache = {};
function setH(id, html) { if (hudCache[id] !== html) { hudCache[id] = html; $(id).innerHTML = html; } }
function showMsg(t, dur) { $('msg').textContent = t; msgT = dur || 2.5; }
function esc(s) { return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c])); }
function loadoutHTML() {
  const rows = L.weapons.map((x, i) => { const d = WEAPONS[x.id]; return `<tr class="${i === L.wi ? 'on' : ''}"><td>${i + 1}</td><td><b>${esc(wName(x))}</b></td><td>${Math.round(dmgOf(x))}${d.pellets > 1 ? ' × ' + d.pellets : ''} dmg</td><td>${d.rpm} rpm</td><td>${x.ammo} / ${magOf(x)} &nbsp;+ ${x.reserve}</td><td>${x.up ? 'Upgraded' : d.burst ? 'Burst' : d.auto ? 'Auto' : 'Semi'}</td></tr>`; }).join('');
  return `<h2>LOADOUT</h2><div class="sk">${esc(me.name)} &nbsp;·&nbsp; ${SKINS[L.skin].name} &nbsp;·&nbsp; wave ${G.round} &nbsp;·&nbsp; ${me.points} points &nbsp;·&nbsp; ${me.kills} kills</div><table>${rows}${L.weapons.length < 2 ? '<tr><td>2</td><td colspan="5">Empty — buy a gun from a rack or a Mystery Crate</td></tr>' : ''}<tr><td>V</td><td><b>Combat knife</b></td><td>160 dmg</td><td colspan="3">120 points a kill</td></tr></table><div class="sk">Health ${Math.round(me.hp)} / ${me.maxHp}${me.maxHp > 100 ? ' (Field Stim)' : ''}</div>`;
}
function updateHUD(dt) {
  const w = curW(), d = WEAPONS[w.id]; musicUpdate(dt);
  setH('load', L.weapons.map((x, i) => `<div class="${i === L.wi ? 'on' : ''}"><b>${i + 1}</b>${esc(wName(x))} <span>${x.ammo}/${x.reserve}</span></div>`).join('') + '<div><b>V</b>Knife</div>');
  $('stbar').style.width = (L.stam * 100) + '%'; $('st').style.opacity = L.stam < .99 ? 1 : 0;
  const tb = !!keys.Tab; if (hudCache.tb !== tb) { hudCache.tb = tb; $('tabp').style.display = tb ? 'block' : 'none'; } if (tb) setH('tabp', loadoutHTML());
  if (L.abRound !== G.round) { const first = L.abRound < 0 || G.round < L.abRound; L.abRound = G.round; if (first || G.round % 2 === 1) for (const b of aboxes) { b.taken = false; b.g.visible = true; } }
  const mv = keys.KeyW || keys.KeyA || keys.KeyS || keys.KeyD, gap = Math.round(clamp(3 + spreadNow(d, mv) * 520, 3, 44)); if (hudCache.gap !== gap) { hudCache.gap = gap; $('cross').style.setProperty('--g', gap + 'px'); }
  setH('wname', wName(w)); setH('am', String(w.ammo)); setH('rs', ' / ' + w.reserve);
  $('am').style.color = w.ammo <= magOf(w) * .25 ? '#e04040' : '#f0f0e8';
  setH('round', G.round > 0 ? String(G.round) : '');
  const left = G.host ? G.toSpawn + zombies.length : (G.left || 0);
  setH('left', G.state === 'wave' ? left + ' remaining' : G.round > 0 ? 'Next wave incoming' : 'They are coming');
  setH('scores', Object.values(players).sort((a, b) => b.points - a.points).map(p => `<div class="${p.id === G.myId ? 'me' : ''} ${p.down ? 'down' : ''}">${esc(p.name)}${p.down ? ' (down)' : ''} &nbsp; ${p.points}</div>`).join(''));
  $('hpbar').style.width = Math.max(0, me.hp / me.maxHp * 100) + '%'; $('hpbar').style.background = me.hp < me.maxHp * .4 ? '#c03030' : '#b8c4a0';
  $('hurt').style.opacity = Math.min(1, L.hurt * .8 + (me.down ? .8 : Math.max(0, 1 - me.hp / me.maxHp) * .7));
  const danger = me.down ? 0 : Math.max(1 - me.hp / me.maxHp, clamp((9 - L.nearZ) / 9, 0, 1) * .8);
  if (danger > .3) { L.hbT -= dt; if (L.hbT <= 0) { L.hbT = 1.15 - danger * .65; sHeart(.4 + danger * .6); } }
  const sat = (.78 - Math.max(0, 1 - me.hp / me.maxHp) * .6).toFixed(2); if (hudCache.sat !== sat) { hudCache.sat = sat; $('c').style.filter = 'saturate(' + sat + ') contrast(1.08)'; }
  $('hit').style.opacity = L.hitFx; $('cross').style.opacity = L.ads > .5 || me.down ? 0 : 1;
  const it = nearestInteractable(); setH('prompt', me.down ? 'You are dead. No revives — you come back if a team-mate survives to the next wave.' + (L.spec ? ' Watching ' + esc(L.spec) : '') : it ? promptFor(it) : '');
  setH('power', G.evacT > 0 ? 'EXTRACTION IN ' + Math.ceil(G.evacT) + (EVAC && (me.l || 0) !== EVAC.l ? ' — GET TO THE ROOF' : '') : G.insta > 0 ? 'OVERKILL ' + Math.ceil(G.insta) : '');
  setH('obj', objText());
  if (G.round !== lastRound) { if (G.round > 0) { showMsg('WAVE ' + G.round, 3.5); sSiren(.1, 6.5); setTimeout(() => sClang(.6, 0), 1100); } lastRound = G.round; }
  if (msgT > 0) { msgT -= dt; $('msg').style.opacity = Math.min(1, msgT * 2); } else $('msg').style.opacity = 0;
  $('lockhint').style.display = document.pointerLockElement || G.over ? 'none' : 'block';
}
function gameOver(won) {
  document.exitPointerLock && document.exitPointerLock();
  $('overtitle').textContent = won ? 'EXTRACTED' : 'YOU DIED'; $('again').textContent = won ? 'Play again' : 'Try again'; $('over').style.background = won ? 'rgba(0,18,8,.82)' : '';
  $('overtext').textContent = won ? `You made it out after ${G.round} wave${G.round === 1 ? '' : 's'} — ${me.kills} kills` : `You survived ${Math.max(0, G.round - 1)} wave${G.round - 1 === 1 ? '' : 's'} — ${me.kills} kills`;
  $('over').style.display = 'flex';
}

// ---------------------------------------------------------------- networking setup
const status = t => { $('status').textContent = t; };
function lockMouse() { try { const r = renderer.domElement.requestPointerLock(); if (r && r.catch) r.catch(() => {}); } catch (e) {} }
function beginGame(isHost, id) {
  initAudio(); G.host = isHost; G.myId = id; G.started = true;
  me = players[id] = newPlayer(id, ($('name').value || 'Survivor').slice(0, 14)); me.x = SPAWN.x + (isHost ? 0 : rnd(-1.5, 1.5)); me.z = SPAWN.z + (isHost ? 0 : rnd(-1.5, 1.5)); me.yaw = Math.PI; L.lastHp = me.hp; me.sk = L.skin;
  if (MAT.gSleeve) MAT.gSleeve.color.set(SKINS[L.skin].cloth).lerp(_white, .45);
  L.weapons = []; giveWeapon('pistol'); L.switchT = 0;
  $('menu').style.display = 'none'; $('hud').style.display = 'block'; camera.fov = 72; camera.updateProjectionMatrix();
  lockMouse();
}
function hostOnline() {
  if (typeof Peer === 'undefined') return status('Online play needs an internet connection (could not load the network library).');
  if (Net.peer) return; status('Creating room…'); const code = Array.from({ length: 5 }, () => 'ABCDEFGHJKLMNPQRSTUVWXYZ'[(Math.random() * 24) | 0]).join('');
  const peer = Net.peer = new Peer('hollowward-' + code);
  peer.on('open', () => { G.code = code; beginGame(true, 'h');
    const tag = t => { $('code').innerHTML = 'ROOM CODE: <b style="color:#dfd;font-size:17px;letter-spacing:4px">' + code + '</b> — up to 4 players, friends enter this to join' + t; }; tag('');
    try { navigator.clipboard.writeText(location.origin + location.pathname + '?join=' + code).then(() => tag(' (invite link copied)'), () => {}); } catch (e) {} });
  peer.on('connection', c => {
    c.on('open', () => { Net.conns[c.peer] = c; c.seen = performance.now(); });
    c.on('data', m => { c.seen = performance.now(); if (Net.conns[c.peer] === c) hostRecv(c.peer, m); });
    c.on('close', () => dropClient(c.peer)); c.on('error', () => dropClient(c.peer));
  });
  peer.on('disconnected', () => { try { peer.reconnect(); } catch (e) {} });   // lost the signalling server: existing players stay connected, this lets new ones join again
  peer.on('error', e => { if (!G.started) { Net.peer = null; status('Could not create room: ' + (e.type || e)); } });
}
function joinOnline() {
  if (typeof Peer === 'undefined') return status('Online play needs an internet connection (could not load the network library).');
  const code = $('joincode').value.trim().toUpperCase(); if (code.length !== 5) return status('Enter the 5-letter room code from the host.');
  if (Net.peer) { try { Net.peer.destroy(); } catch (e) {} } Net.full = false; status('Connecting…'); const peer = Net.peer = new Peer();
  peer.on('open', id => { const c = Net.conn = peer.connect('hollowward-' + code, { reliable: true });
    c.on('open', () => { status('Joining…'); c.send({ t: 'hello', name: ($('name').value || 'Survivor').slice(0, 14), sk: L.skin });
      setTimeout(() => { if (!G.started) status('The host did not answer. Check the code and try again.'); }, 10000); });
    c.on('data', m => { Net.lastRecv = performance.now();
      if (G.started) return clientRecv(m);
      if (m && m.t === 'full') { Net.full = true; return status('That game is full (4 players) or already over.'); }
      if (m && m.t === 'w') { loadMap(String(m.map)); beginGame(false, id); for (const ch of String(m.doors || '')) if (DOORS[ch]) openDoor(ch); $('code').textContent = 'ROOM ' + code + ' — ' + MAPS[MAPID].name; } });
    c.on('close', () => { if (G.started) hostLost(); else if (!Net.full) status('Could not join that game.'); }); });
  peer.on('error', e => { if (!G.started) status(e.type === 'peer-unavailable' ? 'No game found with that code.' : 'Connection failed: ' + (e.type || e)); });
}
addEventListener('beforeunload', () => { try { if (Net.peer) Net.peer.destroy(); } catch (e) {} });

// ---------------------------------------------------------------- init
function init() {
  if (typeof THREE === 'undefined') { status('Could not load the 3D engine. Check your internet connection and reload.'); return; }
  renderer = new THREE.WebGLRenderer({ canvas: $('c'), antialias: true, powerPreference: 'high-performance' });
  maxPR = Math.min(devicePixelRatio || 1, 2); curPR = Math.min(maxPR, 1.5); renderer.setPixelRatio(curPR); renderer.setSize(innerWidth, innerHeight);
  renderer.shadowMap.enabled = true; renderer.shadowMap.autoUpdate = false; renderer.info.autoReset = false; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 1.07; renderer.outputEncoding = THREE.sRGBEncoding; renderer.autoClear = false;
  scene = new THREE.Scene(); scene.background = new THREE.Color(0x04060a); scene.fog = new THREE.FogExp2(0x04060a, .055);
  camera = new THREE.PerspectiveCamera(72, innerWidth / innerHeight, .05, 200); camera.rotation.order = 'YXZ'; scene.add(camera);
  clock = new THREE.Clock(); raycaster = new THREE.Raycaster();
  flashlight = new THREE.SpotLight(0xfff1d6, 2.3, 34, .5, .65, 1.3); flashlight.position.set(.22, -.18, 0); flashlight.castShadow = true;
  flashlight.shadow.mapSize.set(1024, 1024); flashlight.shadow.camera.near = .3; flashlight.shadow.camera.far = 34; flashlight.shadow.bias = -.002;
  camera.add(flashlight); flashlight.target.position.set(0, 0, -6); camera.add(flashlight.target);
  muzzleLight = new THREE.PointLight(0xffc070, 0, 16, 1.5); muzzleLight.position.set(0, 0, -1); camera.add(muzzleLight);
  remoteFlash = new THREE.PointLight(0xffc070, 0, 14, 1.5); scene.add(remoteFlash);
  zGroup = new THREE.Group(); scene.add(zGroup);
  initGeo(); initLevelMats(); buildWeaponScene(); buildFX(); buildShots(); loadMap('ward');
  // film grain
  const gc = document.createElement('canvas'); gc.width = gc.height = 128; const gg = gc.getContext('2d'), gd = gg.createImageData(128, 128);
  for (let i = 0; i < gd.data.length; i += 4) { const v = Math.random() * 255; gd.data[i] = gd.data[i + 1] = gd.data[i + 2] = v; gd.data[i + 3] = 255; } gg.putImageData(gd, 0, 0);
  $('grain').style.backgroundImage = 'url(' + gc.toDataURL() + ')';
  setInterval(() => { $('grain').style.backgroundPosition = ((Math.random() * 128) | 0) + 'px ' + ((Math.random() * 128) | 0) + 'px'; }, 60);

  addEventListener('resize', () => { renderer.setSize(innerWidth, innerHeight); camera.aspect = wcam.aspect = innerWidth / innerHeight; camera.updateProjectionMatrix(); wcam.updateProjectionMatrix(); });
  addEventListener('keydown', e => {
    if (e.target.tagName === 'INPUT') return; keys[e.code] = true; if (!G.started || G.over) return;
    if (e.code === 'Tab' || e.code === 'Space') e.preventDefault();
    if (e.code === 'KeyR') startReload(); if (e.code === 'Digit1') switchWeapon(0); if (e.code === 'Digit2') switchWeapon(1);
    if (e.code === 'KeyF') { L.flash = !L.flash; sTone(1800, .03, .1, 'square'); } if (e.code === 'KeyV' || e.code === 'KeyQ') melee();
    if (e.code === 'KeyE') { const it = nearestInteractable(); if (it) requestBuy(it); }
    if (e.code === 'KeyM' && musicG) { musicOn = !musicOn; musicG.gain.value = musicOn ? .9 : 0; showMsg(musicOn ? 'MUSIC ON' : 'MUSIC OFF', 1.2); }
  });
  addEventListener('keyup', e => { keys[e.code] = false; });
  addEventListener('blur', () => { for (const k in keys) keys[k] = false; mouse.l = mouse.r = false; });
  const cv = renderer.domElement;
  cv.addEventListener('mousedown', e => { if (!G.started || G.over) return; if (!document.pointerLockElement) { lockMouse(); return; } if (e.button === 0) mouse.l = true; if (e.button === 2) mouse.r = true; if (e.button === 1) { e.preventDefault(); melee(); } });
  addEventListener('mouseup', e => { if (e.button === 0) mouse.l = false; if (e.button === 2) mouse.r = false; });
  addEventListener('contextmenu', e => e.preventDefault());
  addEventListener('wheel', () => { if (G.started && L.weapons.length > 1) switchWeapon(1 - L.wi); });
  addEventListener('mousemove', e => { if (!me || me.down || document.pointerLockElement !== cv) return; const s = .0022 / (1 + (WEAPONS[curW().id].zoom - 1) * L.ads);
    L.swx += e.movementX; L.swy += e.movementY; me.yaw -= e.movementX * s; me.pitch = Math.max(-1.5, Math.min(1.5, me.pitch - e.movementY * s)); });
  $('solo').onclick = () => beginGame(true, 'h'); $('host').onclick = hostOnline; $('join').onclick = joinOnline;
  for (const id in MAPS) { const b = document.createElement('button'); b.className = 'mapbtn' + (id === MAPID ? ' sel' : ''); b.innerHTML = '<b>' + MAPS[id].name + '</b><span>' + MAPS[id].desc + '</span>';
    b.onclick = () => { if (G.started || id === MAPID) return; loadMap(id); document.querySelectorAll('.mapbtn').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); }; $('maps').appendChild(b); }
  try { L.skin = clamp(parseInt(localStorage.getItem('hwSkin')) || 0, 0, SKINS.length - 1); } catch (e) {}
  SKINS.forEach((S, i) => { const b = document.createElement('button'); b.className = 'mapbtn skbtn' + (i === L.skin ? ' sel' : ''); const hx = n => '#' + n.toString(16).padStart(6, '0');
    b.innerHTML = '<i style="background:linear-gradient(180deg,' + hx(S.hat === 'bare' ? 0x3a2c22 : S.head) + ' 0 28%,' + hx(S.vest) + ' 28% 62%,' + hx(S.cloth) + ' 62% 76%,' + hx(S.pants) + ' 76%)"></i><b>' + S.name + '</b>';
    b.onclick = () => { if (G.started) return; L.skin = i; try { localStorage.setItem('hwSkin', i); } catch (e) {} document.querySelectorAll('.skbtn').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); }; $('skins').appendChild(b); });
  const jq = new URLSearchParams(location.search).get('join'); if (jq) { $('joincode').value = jq.toUpperCase().slice(0, 5); status('Invite code filled in — press Join game.'); }
  window.HW = { chunks, perf: () => ({ pr: curPR, ms: frameMs, tris: renderer.info.render.triangles, calls: renderer.info.render.calls }), zbuf, snd: { sGroan, sSnarl, sScream, sHiss, sGurgle, sSpawn, sFlesh, sHurt, sSiren, sPowerDown }, ghost, ambush, scareFace, SKINS, musicState: () => ({ tension, mNext, on: musicOn, ok: !!musicG }), hostBuy, obj: () => OBJ, killZombie, G, players, zombies, L, Net, MAPS, loadMap, hostHit, spawnZombie, drops, fire, melee, dealHit, camera: () => camera, WEAPONS, giveWeapon, navStep, groundY, tileL, moveCollide, map: () => ({ MAP, LAYERS, NL, EVAC, W, H, id: MAPID, spawn: SPAWN, zSpawns, colliders, lightSpots, interactables, navBlock, flow }) };
  frame();
}
let lastFrame = 0, lastTick = 0, frameN = 0, frameMs = 16, prT = 0, maxPR = 2, curPR = 1.5;
// keep the simulation alive when the tab is in the background (so a host who tabs away does not freeze everyone)
setInterval(() => {
  const now = performance.now(); if (!G.started || now - lastFrame < 250) { lastTick = now; return; }
  const steps = Math.min(20, Math.round((now - Math.max(lastTick, lastFrame)) / 50)); lastTick = now;
  for (let i = 0; i < steps; i++) { G.time += .05; if (G.host) hostUpdate(.05); else clientUpdate(.05); }
}, 100);
function frame() {
  requestAnimationFrame(frame); lastFrame = performance.now(); let rem = Math.min(clock.getDelta(), .25), tot = 0;
  if (!G.started) { const dt = Math.min(rem, .05); G.time += dt; const a = G.time * .12; camera.position.set(SPAWN.x + Math.cos(a) * 3, 1.7, SPAWN.z + Math.sin(a) * 3); camera.rotation.set(0, -a + Math.PI, 0); updateFX(dt); }
  else {
    do { const dt = Math.min(rem, .05); rem -= dt; tot += dt; G.time += dt; updateLocal(dt); if (G.host) hostUpdate(dt); else clientUpdate(dt); updateViews(dt); } while (rem > .002);
    updateFX(tot); updateHUD(tot);
  }
  renderer.info.reset(); renderer.shadowMap.needsUpdate = (frameN++ & 1) === 0;   // the torch's shadows are redrawn every other frame
  { const now = performance.now(), ms = now - (frame.last || now); frame.last = now; if (ms < 200) { frameMs += (ms - frameMs) * .05; if (now - prT > 1500 && !document.hidden) { prT = now;   // trade sharpness for smoothness when the frame rate drops
      const want = frameMs > 23 ? Math.max(.75, curPR - .15) : frameMs < 14.5 ? Math.min(maxPR, curPR + .1) : curPR; if (Math.abs(want - curPR) > .01) { curPR = want; renderer.setPixelRatio(curPR); } } } }
  renderer.clear(); renderer.render(scene, camera);
  if (G.started && me && !me.down) { renderer.clearDepth(); renderer.render(wscene, wcam); }
}
init();
})();
