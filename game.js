'use strict';
(function () {
const $ = id => document.getElementById(id);
const TILE = 3, WALL_H = 3.6, EYE = 1.66, MAX_ALIVE = 24;

// ---------------------------------------------------------------- map state
let MAP = [['#']], W = 1, H = 1, DOORS = {}, THEME = null, MAPID = 'ward', bldF = null, navBlock = new Uint8Array(1);
const COST = { crate: 950, ammo: 500, stim: 2500 };
const doorOpen = {}, doorMesh = {};
const SOLID = { '#': 1, B: 1, T: 1, R: 1, J: 1 }, OPEN = { '.': 1, ',': 1, '=': 1 }, HARD = { '#': 1, B: 1, R: 1 };
const N4 = [[1, 0], [-1, 0], [0, 1], [0, -1]];
const isDoor = ch => ch >= 'a' && ch <= 'f';
const tileAt = (c, r) => (c < 0 || r < 0 || c >= W || r >= H) ? '#' : MAP[r][c];
function solid(c, r) {
  const ch = tileAt(c, r);
  if (SOLID[ch]) return true;
  if (DOORS[ch] && !doorOpen[ch]) return true;
  return false;
}
// zombies also path around big props (cars, crate, stations) that sit in an otherwise open tile
const navSolid = (c, r) => solid(c, r) || navBlock[r * W + c] === 1;
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
  lmg:     { name: 'Hammer LMG',    dmg: 55,  rpm: 680, auto: true,  mag: 100, reserve: 300, spread: .020, reload: 4.2, pellets: 1, kick: .018, zoom: 1.3 }
};

// ---------------------------------------------------------------- state
let scene, camera, renderer, wscene, wcam, clock, raycaster;
const G = { started: false, host: true, myId: 'h', round: 0, state: 'inter', interT: 6, toSpawn: 0, spawnT: 0, insta: 0, time: 0, over: false, code: '' };
const players = {}; let me = null;
const zombies = [], zById = {}, corpses = []; let zSeq = 1;
const drops = []; let dropSeq = 1;
const L = { vy: 0, onGround: true, bob: 0, weapons: [], wi: 0, fireT: 0, reloadT: 0, switchT: 0, ads: 0, kick: 0, fired: false,
  meleeT: 0, meleeHit: false, flash: true, crateT: 0, crateW: null, lastHp: 100, hurt: 0, wasDown: false, hitFx: 0, sprint: false, stepPh: 0 };
const keys = {}, mouse = { l: false, r: false };
const Net = { peer: null, conns: {}, conn: null, sendT: 0 };
let flashlight, muzzleLight, remoteFlash, zGroup, propGroup, doorGroup, shootables = [];
let crateObj = null, msgT = 0, flow = new Int16Array(W * H), flowT = 0;
const gunViews = {}; let gunRoot, muzzleFlash, wLight, knife;
const rnd = (a, b) => a + Math.random() * (b - a);
const lerpAngle = (a, b, t) => { let d = ((b - a + Math.PI) % (Math.PI * 2) + Math.PI * 2) % (Math.PI * 2) - Math.PI; return a + d * Math.min(1, t); };
function seeded(s) { return () => { s = (s * 16807 + 11) % 2147483647; return (s & 0xffff) / 0x10000; }; }

// ---------------------------------------------------------------- audio
let AC = null, master = null, noiseBuf = null;
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
    for (const fr of [46, 49.5]) { const o = AC.createOscillator(); o.frequency.value = fr; const og = AC.createGain(); og.gain.value = .05; o.connect(og).connect(master); o.start(); }
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
function sShot(kind, vol) {
  const P = SHOT[kind] || SHOT.pistol; vol = vol === undefined ? 1 : vol; if (vol < .02) return;
  sNoise(P[0], P[1], P[2] * vol); sNoise(300, .6, .18 * vol); sTone(150, .14, .7 * vol, 'sine', 0, 40);
}
function sGroan(vol) {
  if (!AC || vol < .02) return; const t = AC.currentTime, d = rnd(.7, 1.6), f0 = rnd(55, 110);
  const o = AC.createOscillator(); o.type = 'sawtooth'; o.frequency.setValueAtTime(f0, t); o.frequency.linearRampToValueAtTime(f0 * rnd(.6, 1.5), t + d);
  const lfo = AC.createOscillator(); lfo.frequency.value = rnd(17, 34); const lg = AC.createGain(); lg.gain.value = 14; lfo.connect(lg).connect(o.frequency);
  const f = AC.createBiquadFilter(); f.type = 'bandpass'; f.frequency.value = rnd(420, 900); f.Q.value = 2.5;
  const g = AC.createGain(); g.gain.setValueAtTime(.0001, t); g.gain.linearRampToValueAtTime(.55 * vol, t + .12); g.gain.exponentialRampToValueAtTime(.001, t + d);
  o.connect(f).connect(g).connect(master); o.start(t); lfo.start(t); o.stop(t + d + .1); lfo.stop(t + d + .1);
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
let levelGroup = null, glowMesh = null, skyGroup = null, hemi = null, sun = null, lightT = 0;
const lightSpots = [], pool = [], weatherPts = [];
let LR = Math.random;                         // seeded while a map is generated, so every player builds the identical level
const lr = (a, b) => a + LR() * (b - a), lpick = n => (LR() * n) | 0;
let instQ = {}, wallQ = {}, glowQ = [];
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
  pine: K => { K.c(.1, .2, 2.6, 0, 1.3, 0, 0x241a12, 7);
    for (let i = 0; i < 5; i++) { const r = 1.75 - i * .32, y = 1.9 + i * 1.05; K.g(new THREE.ConeGeometry(r, 1.7, 9), M(0, y + .85, 0, 0, i * .7, 0), 0x15231a).g(new THREE.ConeGeometry(r * .78, .9, 9), M(0, y + 1.32, 0, 0, i * .7 + .3, 0), 0xaab6c6); } },
  dtree: K => { K.c(.1, .26, 4.6, 0, 2.3, 0, 0x1c1712, 7).c(.3, .36, .3, 0, .15, 0, 0x1c1712, 7);
    for (let i = 0; i < 8; i++) { const a = i * 2.4, h = 2.2 + i * .34, l = 1.9 - i * .14, bx = Math.cos(a) * l, bz = Math.sin(a) * l;
      K.seg(.07, .03, [0, h, 0], [bx, h + l * .55, bz], 0x1c1712).seg(.03, .012, [bx * .6, h + l * .33, bz * .6], [bx * .7 + bz * .4, h + l * .9, bz * .7 - bx * .4], 0x1c1712, 5).seg(.03, .01, [bx, h + l * .55, bz], [bx * 1.3, h + l * 1.1, bz * 1.3], 0x1c1712, 5); } },
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
  roof: K => { const g = new THREE.BufferGeometry(), A = [-.5, 0, -.5], B = [.5, 0, -.5], C = [0, 1, -.5], D = [-.5, 0, .5], E = [.5, 0, .5], F = [0, 1, .5];
    g.setAttribute('position', new THREE.Float32BufferAttribute([].concat(D, E, F, B, A, C, A, D, F, A, F, C, B, F, E, B, C, F, A, B, E, A, E, D), 3)); g.computeVertexNormals(); K.g(g, null, 0xffffff); },
  barricade: K => { K.b(.2, 3.6, .22, -1.4, 1.8, 0, 0x2a2018).b(.2, 3.6, .22, 1.4, 1.8, 0, 0x2a2018).b(3.0, .22, .22, 0, 3.49, 0, 0x2a2018).b(3.0, .16, .26, 0, .08, 0, 0x2a2018);
    for (let i = 0; i < 6; i++) { const h = [3.3, 2.7, 3.4, 3.0, 3.38, 2.5][i]; K.b(.4, h, .05, -1.15 + i * .46, h / 2, (i % 2) * .05 - .02, [0x4a3826, 0x3e2e1e, 0x54402c][i % 3], 0, 0, (i % 3 - 1) * .02); }
    K.b(3.1, .26, .05, 0, 2.5, .09, 0x5c4630, 0, 0, .3).b(3.1, .26, .05, 0, 1.3, .09, 0x4c3a28, 0, 0, -.26).b(3.0, .24, .05, 0, .7, -.09, 0x5c4630, 0, 0, .08).b(2.9, .22, .05, 0, 2.1, -.09, 0x443424, 0, 0, -.12).b(1.1, .8, .02, .5, 1.75, .13, 0x4a3a30, 0, 0, .1);
    for (let i = 0; i < 8; i++) K.c(.012, .012, .03, -1.3 + i * .37, 1.3 - (i - 3.5) * .09, .12, 0x9a9a9a, 5, Math.PI / 2, 0, 0); }
};
const METAL = { car: 1, van: 1, lamp: 1, rail: 1, dumpster: 1, locker: 1, barrel: 1, pump: 1 }, NOSHADOW = { drift: 1, deb: 1 };
function kitGeo(name) { if (!KGEO[name]) { const K = Kit(); KITS[name](K); const g = K.done(); g.userData.keep = true; KGEO[name] = g; } return KGEO[name]; }
function wallGeo(kind) {
  const key = 'w_' + kind; if (KGEO[key]) return KGEO[key];
  const K = Kit(), T = TILE, h = WALL_H, y0 = -h / 2, cross = (w, hh, y, col) => { K.b(T + w, hh, T, 0, y, 0, col).b(T, hh, T + w, 0, y, 0, col); };
  K.g(new THREE.BoxGeometry(T, h, T, 1, 4, 1), null, 0xffffff);
  if (kind === 'in') { cross(.1, .2, y0 + .1, 0x5a564c); cross(.05, .07, y0 + 1.02, 0x8a877c); cross(.12, .14, h / 2 - .07, 0x8f8c80); }
  if (kind === 'rib') { cross(.16, .5, y0 + .25, 0x858585); cross(.22, .24, h / 2 - .12, 0x9a9a9a); K.b(.55, h, T + .18, 0, 0, 0, 0xb4b4b4).b(T + .18, h, .55, 0, 0, 0, 0xb4b4b4); }
  if (kind === 'plank') { cross(.14, .24, y0 + .12, 0x5a4a3a); cross(.14, .24, h / 2 - .12, 0x5a4a3a); cross(.07, .13, .1, 0x74624c); K.b(.26, h, T + .13, 0, 0, 0, 0x64523e).b(T + .13, h, .26, 0, 0, 0, 0x64523e); }
  if (kind === 'brick') { cross(.14, .62, y0 + .31, 0x7c7e80); cross(.18, .28, h / 2 - .14, 0x8e9092); K.b(.7, h, T + .1, 0, 0, 0, 0xc4c0bc).b(T + .1, h, .7, 0, 0, 0, 0xc4c0bc); }
  if (kind === 'facade') cross(.32, .2, y0 + .1, 0x9a9c9e);
  const g = K.done(), p = g.attributes.position, c = g.attributes.color;
  for (let i = 0; i < p.count; i++) { const y = p.getY(i), f = kind === 'facade' ? 1 : y < -.9 ? .45 + .55 * (y + 1.8) / .9 : y > .9 ? 1 - .4 * (y - .9) / .9 : 1; c.setXYZ(i, c.getX(i) * f, c.getY(i) * f, c.getZ(i) * f); }
  g.userData.keep = true; return KGEO[key] = g;
}
const put = (kind, x, y, z, ry, sx, sy, sz, col, rx, rz) => { (instQ[kind] = instQ[kind] || []).push([M(x, y, z, rx, ry, rz, sx, sy, sz), col]); };
const pushW = (mat, geo, x, y, z) => { const k = mat + '|' + geo; (wallQ[k] = wallQ[k] || []).push([x, y, z]); };
function glow(x, y, z, sx, sy, sz, hex, ry) { glowQ.push([M(x, y, z, 0, ry, 0, sx, sy, sz), hex]); return glowQ.length - 1; }
function spot(x, y, z, col, base, range, mode, gi) {
  const s = { x, y, z, col: new THREE.Color(col), base, range, mode: mode || 0, ph: LR() * 99, v: 1, gi: gi === undefined ? -1 : gi, gc: null, a: 0, pl: -1, d: 0 };
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
  for (let i = 0; i < 8; i++) { const p = new THREE.Points(wg, MAT.weather); p.frustumCulled = false; p.visible = false; scene.add(p); weatherPts.push(p); }
}

// ---------------------------------------------------------------- map generators
function Gen(w, h, fill) {
  const g = []; for (let r = 0; r < h; r++) g.push(new Array(w).fill(fill));
  const props = [], used = new Uint8Array(w * h);
  const G = { g, props, w, h, spawn: { c: 1, r: 1 }, bld: null,
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
  };
  return G;
}
const CARCOL = [0x6a1f1c, 0x26384e, 0x8a8c8a, 0x2c2e30, 0x7a6a44, 0x39503c, 0xa8a69c, 0x4a2c50];
function addCar(G, c, r, ry) { const burnt = LR() < .24; G.add('car', c, r, { ry, van: LR() < .22, col: burnt ? 0x1a1612 : CARCOL[lpick(CARCOL.length)], fire: burnt && LR() < .45, tilt: burnt ? lr(-.06, .06) : 0, sink: burnt }); }
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
  G.clutter(['bed', 'bed', 'bed', 'locker', 'cabinet', 'desk', 'chair', 'shelf'], 40, ch => ch === '.');
  G.clutter(['bench', 'box', 'barrel'], 5, ch => ch === ',');
  G.scatter('deb', 150, ch => ch === '.'); G.scatter('rubble', 8, ch => ch === '.'); G.scatter('deb', 40, ch => ch === ',');
  return G;
}
function genWoods() {
  const n = 46, G = Gen(n, n, ','), g = G.g;
  for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (c < 2 || r < 2 || c > 43 || r > 43) g[r][c] = 'T';
  for (let i = 0; i < 50; i++) { const k = 2 + lpick(42), s = lpick(4); G.set(s === 0 ? 2 : s === 1 ? 43 : k, s === 2 ? 2 : s === 3 ? 43 : k, 'T'); }
  G.spawn = { c: 23, r: 29 }; G.reserve(23, 29, 2);
  // cabin
  G.frame(20, 18, 26, 23, '#'); G.rect(21, 19, 25, 22, '.'); G.set(23, 23, 'a'); G.reserve(23, 20, 5);
  G.add('ammo', 21, 19).add('light', 23, 20, { m: 1 }).add('bed', 25, 20, { dx: 1, dz: 0 }).add('desk', 23, 19, { dx: 0, dz: -1 }).add('shelf', 21, 21, { dx: -1, dz: 0 }).add('chair', 25, 22, { dx: 0, dz: 1 });
  G.deco({ k: 'roof', x: wx(23), z: (wx(18) + wx(23)) / 2, sx: 7 * TILE + 1.4, sz: 6 * TILE + 1.4, h: 2.8 });
  // shed
  G.frame(35, 8, 39, 12, '#'); G.rect(36, 9, 38, 11, '.'); G.set(35, 10, 'b'); G.reserve(37, 10, 4);
  G.add('stim', 38, 10).add('light', 37, 10, { m: 1 }).add('box', 37, 9, { dx: 0, dz: -1 });
  G.deco({ k: 'roof', x: wx(37), z: wx(10), sx: 5 * TILE + 1.2, sz: 5 * TILE + 1.2, h: 2.2 });
  G.add('crate', 9, 35); G.reserve(9, 35, 2);
  G.deco({ k: 'lantern', x: wx(9) + 2.3, z: wx(35) - 2.3, ry: 2 }).deco({ k: 'lantern', x: wx(23) + 2.2, z: wx(24) - .6, ry: 3.6 }).deco({ k: 'lantern', x: wx(34) - .5, z: wx(10) + 2.2, ry: 5 }).deco({ k: 'lantern', x: wx(30), z: wx(30), ry: 1 }).deco({ k: 'lantern', x: wx(15), z: wx(15), ry: 4 });
  G.deco({ k: 'fire', x: wx(23) + 2.6, z: wx(29) - 2.6 });
  for (const [c, r] of [[5, 5], [23, 4], [40, 5], [4, 23], [41, 24], [5, 40], [23, 41], [40, 40], [13, 14], [33, 30], [12, 28], [32, 17], [16, 38], [36, 36]]) { G.set(c, r, ','); G.add('zs', c, r); G.reserve(c, r, 1); }
  G.add('car', 14, 23, { ry: .6, col: 0x39503c, sink: true }); G.reserve(14, 23, 1); G.add('car', 31, 38, { ry: 2.3, van: true, col: 0x8a8c8a }); G.reserve(31, 38, 1);
  for (let i = 0, k = 0; i < 400 && k < 24; i++) { const c = 4 + lpick(38), r = 4 + lpick(38); if (!G.ring(c, r)) continue; g[r][c] = 'R'; G.reserve(c, r, 1); k++; }
  for (let r = 2; r < 44; r++) for (let c = 2; c < 44; c++) { if (g[r][c] !== ',' || !G.free(c, r) || LR() > .34) continue; const a = lr(0, 6.28), d = lr(.75, 1.15);
    G.deco({ k: LR() < .78 ? 'pine' : 'dtree', x: wx(c) + Math.cos(a) * d, z: wx(r) + Math.sin(a) * d, s: lr(.8, 1.4), ry: lr(0, 6) }); }
  const snow = ch => ch === ','; G.scatter('log', 26, snow); G.scatter('stump', 34, snow); G.scatter('drift', 170, snow); G.scatter('deb', 90, snow);
  return G;
}
function genBack() {
  const n = 41, G = Gen(n, n, '.'), g = G.g; G.frame(0, 0, 40, 40, '#');
  for (let i = 1; i < 40; i++) { g[i][20] = '#'; g[20][i] = '#'; }
  g[10][20] = 'a'; g[20][10] = 'b'; g[20][30] = 'c'; g[30][20] = 'd';
  G.spawn = { c: 6, r: 6 };
  const prot = new Uint8Array(n * n), P = (c, r, rad) => { for (let y = r - rad; y <= r + rad; y++) for (let x = c - rad; x <= c + rad; x++) prot[y * n + x] = 1; };
  P(6, 6, 1); P(20, 10, 2); P(10, 20, 2); P(30, 20, 2); P(20, 30, 2); P(30, 6, 1); P(7, 31, 1); P(31, 31, 1);
  const q = new Int32Array(n * n), seen = new Uint8Array(n * n);
  const walk = () => { seen.fill(0); let h = 0, t = 0; q[t++] = 6 * n + 6; seen[6 * n + 6] = 1;
    while (h < t) { const i = q[h++], c = i % n, r = (i / n) | 0; for (const d of N4) { const x = c + d[0], y = r + d[1], j = y * n + x; if (x < 0 || y < 0 || x >= n || y >= n || seen[j] || g[y][x] === '#') continue; seen[j] = 1; q[t++] = j; } }
    return t; };
  let total = 0; for (let r = 0; r < n; r++) for (let c = 0; c < n; c++) if (g[r][c] !== '#') total++;
  for (let i = 0; i < 300; i++) { const c = 2 + 2 * lpick(19), r = 2 + 2 * lpick(19), hz = LR() < .5, len = 1 + lpick(4), cells = [];
    for (let k = 0; k < len; k++) { const x = c + (hz ? k : 0), y = r + (hz ? 0 : k); if (G.get(x, y) !== '.' || prot[y * n + x]) break; cells.push([x, y]); }
    if (!cells.length) continue; for (const [x, y] of cells) g[y][x] = '#';
    if (walk() !== total - cells.length) { for (const [x, y] of cells) g[y][x] = '.'; } else total -= cells.length; }
  G.reserve(6, 6, 1); G.add('ammo', 30, 6); G.add('stim', 7, 31); G.add('crate', 31, 31); G.reserve(30, 6, 1); G.reserve(7, 31, 1); G.reserve(31, 31, 1);
  for (let r = 2; r < 40; r += 3) for (let c = 2; c < 40; c += 3) if (g[r][c] === '.') G.add('light', c, r, { m: LR() < .12 ? 2 : LR() < .3 ? 1 : 0 });
  for (let qd = 0; qd < 4; qd++) for (let k = 0, t = 0; k < 5 && t < 400; t++) { const c = 2 + lpick(17) + (qd % 2) * 20, r = 2 + lpick(17) + (qd >> 1) * 20; if (!G.free(c, r) || Math.hypot(c - 6, r - 6) < 6) continue; G.add('zs', c, r); k++; }
  G.clutter(['chair', 'desk', 'cabinet', 'shelf', 'box', 'chair'], 34, ch => ch === '.'); G.scatter('deb', 70, ch => ch === '.');
  return G;
}
function genHighway() {
  const w = 21, h = 84, G = Gen(w, h, '#'), g = G.g;
  for (let r = 0; r < 82; r++) { g[r][0] = g[r][1] = 'R'; if (r < 2) { for (let c = 2; c <= 12; c++) g[r][c] = 'R'; continue; }
    g[r][2] = g[r][3] = g[r][11] = g[r][12] = ','; for (let c = 4; c <= 10; c++) g[r][c] = '='; if (r % 8 < 6) g[r][7] = 'J'; }
  for (let c = 2; c <= 12; c++) { g[28][c] = '#'; g[56][c] = '#'; }
  g[28][5] = g[28][6] = 'a'; g[56][9] = g[56][10] = 'b'; g[27][7] = g[29][7] = g[55][7] = g[57][7] = '=';
  G.deco({ k: 'slab', x: 19.5, y: WALL_H + .55, z: wx(28), sx: 39, sy: 1.1, sz: 10, col: 0x6a6c6e }).deco({ k: 'slab', x: 19.5, y: WALL_H + 1.5, z: wx(28) - 4.85, sx: 39, sy: .9, sz: .3, col: 0x5a5c5e }).deco({ k: 'slab', x: 19.5, y: WALL_H + 1.5, z: wx(28) + 4.85, sx: 39, sy: .9, sz: .3, col: 0x5a5c5e });
  // gas station
  G.rect(13, 36, 15, 46, ','); G.rect(17, 39, 18, 43, '.'); g[41][16] = 'c';
  G.add('stim', 18, 39).add('light', 17, 41, { m: 1 }).add('shelf', 18, 43, { dx: 1, dz: 0 }).add('pump', 14, 40).add('pump', 14, 42);
  G.deco({ k: 'slab', x: wx(14), y: 3.6, z: wx(41), sx: 8.4, sy: .4, sz: 15.5, col: 0x8a2a22 });
  for (const a of [[-3.6, -7], [3.6, -7], [-3.6, 7], [3.6, 7]]) G.deco({ k: 'slab', x: wx(14) + a[0], y: 1.7, z: wx(41) + a[1], sx: .28, sy: 3.4, sz: .28, col: 0x9a9a94 });
  G.spawn = { c: 5, r: 78 }; G.reserve(5, 78, 2); G.reserve(5, 28, 2); G.reserve(6, 28, 2); G.reserve(9, 56, 2); G.reserve(10, 56, 2);
  G.add('ammo', 12, 72); G.add('crate', 12, 9); G.reserve(12, 9, 1); G.reserve(12, 72, 1);
  for (const [c, r] of [[2, 60], [12, 61], [3, 80], [2, 69], [11, 66], [9, 59], [2, 32], [12, 32], [2, 50], [12, 53], [3, 42], [9, 31], [2, 4], [12, 4], [2, 20], [12, 22], [6, 3], [9, 14]]) G.add('zs', c, r);
  const carAt = new Uint8Array(w * h);
  for (let r = 3; r < 81; r++) for (let c = 4; c <= 10; c++) { if (g[r][c] !== '=' || !G.free(c, r) || LR() > .17) continue;
    let ok = true; for (let y = -1; y <= 1; y++) for (let x = -1; x <= 1; x++) if (carAt[(r + y) * w + c + x]) ok = false; if (!ok) continue;
    carAt[r * w + c] = 1; addCar(G, c, r, LR() < .2 ? lr(0, 6.28) : (c < 7 ? Math.PI : 0) + lr(-.35, .35)); }
  for (let r = 4; r < 81; r += 6) { const e = (r / 6 | 0) % 2; if (e && r >= 35 && r <= 47) continue; G.deco({ k: 'lamp', x: e ? wx(12) + 1.0 : wx(2) - 1.0, z: wx(r), ry: e ? -Math.PI / 2 : Math.PI / 2, lit: LR() < .45 }); }
  for (let r = 2; r < 82; r++) { if (LR() < .85) G.deco({ k: 'rail', x: 6.4, z: wx(r), ry: 0 }); if (LR() < .85 && (r < 36 || r > 46)) G.deco({ k: 'rail', x: 38.6, z: wx(r), ry: Math.PI });
    if (r % 2 === 0 && r !== 28 && r !== 56) for (const x of [15, 18, 27, 30]) G.deco({ k: 'dash', x, z: wx(r) }); }
  for (const x of [12.2, 20.8, 24.2, 32.8]) G.deco({ k: 'slab', x, y: .012, z: 126, sx: .14, sy: .02, sz: 238, col: 0x8a8778 });
  const dirt = ch => ch === ','; G.clutter(['barrel', 'box', 'tyres', 'dumpster', 'tyres'], 26, dirt);
  G.scatter('dtree', 22, dirt, { s: 1 }); G.scatter('deb', 240, ch => ch !== '#'); G.scatter('rubble', 24, ch => ch !== '#'); G.scatter('cone', 16, ch => ch === '=');
  return G;
}
function genCity() {
  const n = 62, G = Gen(n, n, '='), g = G.g, bld = G.bld = new Uint8Array(n * n);
  G.frame(0, 0, 61, 61, 'B'); for (let i = 0; i < n; i++) bld[i] = bld[61 * n + i] = bld[i * n] = bld[i * n + 61] = 6;
  const building = (c0, r0, c1, r1, fl, ruin, lock, side) => {
    G.frame(c0, r0, c1, r1, 'B'); G.rect(c0 + 1, r0 + 1, c1 - 1, r1 - 1, '.'); for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) bld[r * n + c] = fl;
    const cm = (c0 + c1) >> 1, rm = (r0 + r1) >> 1, mid = s => s === 0 ? [cm, r0] : s === 1 ? [c1, rm] : s === 2 ? [cm, r1] : [c0, rm];
    if (lock) { const m = mid(side); g[m[1]][m[0]] = lock; return; }
    const sides = [lpick(2) * 2, 1 + lpick(2) * 2]; if (LR() < .5) sides.push((sides[0] + 2) % 4);
    for (const s of sides) { const m = mid(s), tall = r1 - r0 >= 4, off = -lpick(2); if (s % 2 === 0) g[m[1]][m[0] + off] = '.'; else g[m[1] + (tall ? off : 0)][m[0]] = '.'; }
    if (ruin) for (let r = r0; r <= r1; r++) for (let c = c0; c <= c1; c++) { const er = r === r0 || r === r1, ec = c === c0 || c === c1; if (er !== ec && LR() < .2) { g[r][c] = '.'; G.deco({ k: 'rubble', x: wx(c) + lr(-.8, .8), z: wx(r) + lr(-.8, .8) }); } }
    if (c1 - c0 >= 6 && r1 - r0 >= 6) { if (LR() < .5) { const gap = r0 + 1 + lpick(r1 - r0 - 1); for (let r = r0 + 1; r < r1; r++) if (r !== gap) g[r][cm + 1] = '#'; } else { const gap = c0 + 1 + lpick(c1 - c0 - 1); for (let c = c0 + 1; c < c1; c++) if (c !== gap) g[rm + 1][c] = '#'; } }
    if (g[r0 + 1][c0 + 1] === '.') G.add('light', c0 + 1, r0 + 1, { m: LR() < .5 ? 2 : 1 }); if (g[r1 - 1][c1 - 1] === '.') G.add('light', c1 - 1, r1 - 1, { m: LR() < .6 ? 2 : 1 });
    if (LR() < .4 && G.free(c1 - 1, r0 + 1)) G.add('zs', c1 - 1, r0 + 1);
  };
  for (let i = 0; i < 5; i++) for (let j = 0; j < 5; j++) G.add('zs', 2 + 12 * i, 2 + 12 * j);
  for (let j = 0; j < 5; j++) for (let i = 0; i < 5; i++) { const c0 = 4 + i * 12, r0 = 4 + j * 12, c1 = c0 + 8, r1 = r0 + 8; G.rect(c0, r0, c1, r1, ',');
    for (const a of [[c0, r0, -1, -1], [c1, r0, 1, -1], [c0, r1, -1, 1], [c1, r1, 1, 1]]) if (LR() < .6) G.deco({ k: 'lamp', x: wx(a[0]) + a[2] * 1.0, z: wx(a[1]) + a[3] * 1.0, ry: Math.atan2(a[2], 0) , lit: LR() < .45 || (i === 2 && j === 2) });
    if (i === 2 && j === 2) { G.spawn = { c: c0 + 4, r: r0 + 4 }; G.reserve(c0 + 4, r0 + 4, 2); G.deco({ k: 'fire', x: wx(c0 + 2), z: wx(r0 + 2), barrel: 1 }).deco({ k: 'fire', x: wx(c1 - 2), z: wx(r1 - 2), barrel: 1 }); continue; }
    if (i === 2 && j === 1) { building(c0 + 1, r0 + 1, c1 - 1, r1 - 1, 3, false, 'a', 2); G.add('ammo', c0 + 4, r0 + 4).add('light', c0 + 4, r0 + 3, { m: 0 }).add('locker', c0 + 2, r0 + 3, { dx: -1, dz: 0 }).add('shelf', c1 - 2, r0 + 3, { dx: 1, dz: 0 }); continue; }
    if (i === 1 && j === 2) { building(c0 + 1, r0 + 1, c1 - 1, r1 - 1, 4, false, 'b', 1); G.add('stim', c0 + 4, r0 + 4).add('light', c0 + 3, r0 + 4, { m: 1 }).add('bed', c0 + 2, r0 + 3, { dx: -1, dz: 0 }).add('cabinet', c0 + 4, r0 + 2, { dx: 0, dz: -1 }); continue; }
    if (i === 3 && j === 3) { G.add('crate', c0 + 4, r0 + 4); G.reserve(c0 + 4, r0 + 4, 1); G.deco({ k: 'lantern', x: wx(c0 + 4) + 2.4, z: wx(r0 + 4) - 2.4, ry: 2 }); continue; }
    const t = LR();
    if (t < .56) building(c0 + 1, r0 + 1, c1 - 1, r1 - 1, 2 + lpick(5), LR() < .35);
    else if (t < .72) { building(c0 + 1, r0 + 1, c1 - 1, r0 + 3, 2 + lpick(3), false); building(c0 + 1, r0 + 5, c1 - 1, r1 - 1, 2 + lpick(3), LR() < .4); }
    else if (t < .86) { G.rect(c0, r0, c1, r1, '='); for (let r = r0 + 1; r < r1; r += 2) for (let c = c0 + 1; c < c1; c += 2) if (LR() < .55) addCar(G, c, r, lr(-.15, .15) + (LR() < .5 ? 0 : Math.PI)); }
    else for (let r = r0 + 1; r < r1; r++) for (let c = c0 + 1; c < c1; c++) if (LR() < .18) G.deco({ k: 'dtree', x: wx(c) + lr(.7, 1.1), z: wx(r) + lr(-1.1, -.7), s: lr(.8, 1.2) });
  }
  const carAt = new Uint8Array(n * n), street = v => (v - 1) % 12 < 3;
  for (let r = 1; r < 61; r++) for (let c = 1; c < 61; c++) { if (g[r][c] !== '=' || !G.free(c, r)) continue; const vs = street(c), hs = street(r); if (!vs && !hs) continue;
    if (!(vs && hs) && ((vs && (c - 1) % 12 === 1 && r % 2) || (hs && (r - 1) % 12 === 1 && c % 2))) G.deco({ k: 'dash', x: wx(c), z: wx(r), ry: vs ? 0 : Math.PI / 2 });
    if (LR() > .075) continue; let ok = true; for (let y = -1; y <= 1; y++) for (let x = -1; x <= 1; x++) if (carAt[(r + y) * n + c + x] || !G.open(c + x, r + y)) ok = false; if (!ok) continue;
    carAt[r * n + c] = 1; addCar(G, c, r, LR() < .25 ? lr(0, 6.28) : (vs ? 0 : Math.PI / 2) + lr(-.3, .3) + (LR() < .5 ? Math.PI : 0)); }
  G.clutter(['dumpster', 'box', 'barrel', 'tyres', 'bench', 'hydrant', 'dumpster'], 70, ch => ch === ',');
  G.clutter(['desk', 'shelf', 'locker', 'cabinet', 'chair', 'bed', 'desk', 'box'], 110, ch => ch === '.');
  G.scatter('deb', 520, ch => true); G.scatter('rubble', 60, ch => true); G.scatter('cone', 14, ch => ch === '=');
  return G;
}
const MAPS = {
  ward: { name: 'Hollow Ward', desc: 'Abandoned hospital', seed: 101, gen: genWard,
    doors: { a: { cost: 750, name: 'the West Ward' }, b: { cost: 1250, name: 'the Courtyard' }, c: { cost: 1000, name: 'the South Hall' }, d: { cost: 1250, name: 'the Morgue' }, e: { cost: 1000, name: 'the Service Corridor' }, f: { cost: 1000, name: 'the Morgue Passage' } },
    theme: { fog: 0x04060a, dens: .055, hemi: [0x31405c, 0x0a0a08, .22], sun: null, wall: ['wallA', 'wallB'], wk: 'in', floor: 'floor', ceil: 'ceil', ground: 'ground', road: 'asphalt', deb: 0x6a6a62, rock: 0x55585a, light: 0xd9e2b0 } },
  woods: { name: 'Winter Woods', desc: 'Snowed-in forest and cabin', seed: 4242, gen: genWoods,
    doors: { a: { cost: 750, name: 'the Cabin' }, b: { cost: 1250, name: 'the Shed' } },
    theme: { fog: 0x121c2a, dens: .036, hemi: [0x7088b4, 0x222630, .6], sun: [0x8fa8d8, .45], wall: ['plank', 'plank'], wk: 'plank', floor: 'woodfloor', ceil: 'woodfloor', ground: 'snow', road: 'snow', deb: 0xaab4c4, rock: 0x70767e, light: 0xffc880, weather: 'snow' } },
  back: { name: 'The Back Rooms', desc: 'Endless yellow maze', seed: 777, gen: genBack,
    doors: { a: { cost: 750, name: 'the East Rooms' }, b: { cost: 750, name: 'the South Rooms' }, c: { cost: 1250, name: 'the Far Rooms' }, d: { cost: 1250, name: 'the Far Rooms' } },
    theme: { fog: 0x17150a, dens: .042, hemi: [0x8a8040, 0x2a2610, .5], sun: null, wall: ['paper', 'paper'], wk: 'in', floor: 'carpet', ceil: 'ctile', ground: 'carpet', road: 'carpet', deb: 0x6a6238, rock: 0x55585a, light: 0xfff0a8, panel: true } },
  highway: { name: 'Dead Highway', desc: 'Ruined road and wrecked cars', seed: 9090, gen: genHighway,
    doors: { a: { cost: 750, name: 'the Overpass' }, b: { cost: 1250, name: 'the Checkpoint' }, c: { cost: 1000, name: 'the Gas Station' } },
    theme: { fog: 0x1c120d, dens: .024, hemi: [0x8a6a5a, 0x1a1410, .8], sun: [0xd88050, .6], wall: ['concrete', 'concrete'], wk: 'rib', floor: 'floor', ceil: 'ceil', ground: 'dirt', road: 'asphalt', deb: 0x4a4a48, rock: 0x4a4440, light: 0xffb060, weather: 'ember' } },
  city: { name: 'Broken City', desc: 'Huge ruined city, enter the buildings', seed: 31337, gen: genCity,
    doors: { a: { cost: 750, name: 'the Armory' }, b: { cost: 1000, name: 'the Clinic' } },
    theme: { fog: 0x10131a, dens: .022, hemi: [0x6a7ca4, 0x16161a, .75], sun: [0x8aa0d0, .5], wall: ['wallA', 'wallB'], wk: 'in', bwall: 'brick', facade: 'facade', floor: 'floor', ceil: 'ceil', ground: 'sidewalk', road: 'asphalt', deb: 0x5a5a58, rock: 0x55585a, light: 0xffc890, weather: 'ember' } }
};

// ---------------------------------------------------------------- level build
function tileMesh(list, y, up, mat, uvS) {
  const pos = [], nor = [], uv = [], col = [], hard = (c, r) => { const ch = tileAt(c, r); return ch === '#' || ch === 'B'; };
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
function loadMap(id) {
  const def = MAPS[id] || MAPS.ward; MAPID = MAPS[id] ? id : 'ward';
  if (levelGroup) { scene.remove(levelGroup); levelGroup.traverse(o => { if (o.geometry && !o.geometry.userData.keep) o.geometry.dispose(); }); }
  levelGroup = new THREE.Group(); scene.add(levelGroup); propGroup = new THREE.Group(); doorGroup = new THREE.Group(); levelGroup.add(propGroup, doorGroup);
  zSpawns.length = 0; interactables.length = 0; colliders.length = 0; lightSpots.length = 0; crateObj = null;
  for (const k in doorOpen) delete doorOpen[k]; for (const k in doorMesh) delete doorMesh[k];
  for (const p of pool) { p.spot = null; p.l.intensity = 0; }
  instQ = {}; wallQ = {}; glowQ = []; LR = seeded(def.seed);
  const d = def.gen(), T = THEME = def.theme;
  MAP = d.g; H = MAP.length; W = MAP[0].length; DOORS = def.doors; bldF = d.bld; flow = new Int16Array(W * H); navBlock = new Uint8Array(W * H); flowT = 0;
  SPAWN = { x: wx(d.spawn.c), z: wx(d.spawn.r) }; shootables = [doorGroup, propGroup, zGroup];
  const fl = {}, ceil = [], pushF = (name, c, r) => { (fl[name] = fl[name] || []).push([c, r, 1]); };
  for (let r = 0; r < H; r++) for (let c = 0; c < W; c++) {
    const ch = MAP[r][c], x = wx(c), z = wx(r);
    if (ch === '#') pushW(T.wall[(c * 7 + r * 13) % 5 === 0 ? 1 : 0], T.wk, x, WALL_H / 2, z);
    else if (ch === 'B') pushW(T.bwall, 'brick', x, WALL_H / 2, z);
    else {
      const indoor = ch === '.' || (isDoor(ch) && N4.some(q => tileAt(c + q[0], r + q[1]) === '.'));
      if (indoor) { pushF(T.floor, c, r); ceil.push([c, r, 1]); } else pushF(ch === '=' || ch === 'J' ? T.road : T.ground, c, r);
      if (isDoor(ch)) addDoor(ch, c, r);
      if (ch === 'T') for (let i = 0, k = 2 + lpick(2); i < k; i++) { const s = lr(1.1, 1.7); put('pine', x + lr(-1.2, 1.2), 0, z + lr(-1.2, 1.2), lr(0, 6), s, s * lr(.9, 1.3), s); }
      if (ch === 'R') put('rock', x + lr(-.3, .3), -.1, z + lr(-.3, .3), lr(0, 6), lr(1.75, 2.15), lr(1.7, 3.4), lr(1.75, 2.15), T.rock);
      if (ch === 'J') put('barrier', x, 0, z, 0);
    }
    const f = bldF ? bldF[r * W + c] : 0;
    if (f && N4.some(q => { const cc = c + q[0], rr = r + q[1]; return cc >= 0 && rr >= 0 && cc < W && rr < H && !bldF[rr * W + cc]; })) for (let k = 1; k < f; k++) pushW(T.facade, 'facade', x, k * WALL_H + WALL_H / 2, z);
  }
  for (const name in fl) { const m = tileMesh(fl[name], 0, true, texMat(name), UVS[name] || 6); levelGroup.add(m); shootables.push(m); }
  if (ceil.length) { const m = tileMesh(ceil, WALL_H, false, texMat(T.ceil), 3); levelGroup.add(m); shootables.push(m); }
  d.props.forEach(placeProp);
  const o = new THREE.Object3D(), tc = new THREE.Color();
  for (const key in wallQ) { const kk = key.split('|'), list = wallQ[key], m = new THREE.InstancedMesh(wallGeo(kk[1]), texMat(kk[0]), list.length);
    list.forEach((p, i) => { o.position.set(p[0], p[1], p[2]); o.updateMatrix(); m.setMatrixAt(i, o.matrix); });
    m.frustumCulled = false; m.receiveShadow = true; m.castShadow = kk[1] !== 'facade'; levelGroup.add(m); if (kk[1] !== 'facade') shootables.push(m); }
  for (const kind in instQ) { const list = instQ[kind], m = new THREE.InstancedMesh(kitGeo(kind), METAL[kind] ? MAT.vcM : MAT.vc, list.length);
    list.forEach((p, i) => { m.setMatrixAt(i, p[0]); m.setColorAt(i, tc.set(p[1] === undefined ? 0xffffff : p[1]).convertSRGBToLinear()); });
    m.frustumCulled = false; m.receiveShadow = true; m.castShadow = !NOSHADOW[kind]; propGroup.add(m); }
  glowMesh = new THREE.InstancedMesh(KGEO.glowBox, MAT.glow, Math.max(1, glowQ.length)); glowMesh.frustumCulled = false;
  if (!glowQ.length) { o.position.set(0, -99, 0); o.updateMatrix(); glowMesh.setMatrixAt(0, o.matrix); glowMesh.setColorAt(0, tc.set(0)); }
  glowQ.forEach((p, i) => { glowMesh.setMatrixAt(i, p[0]); glowMesh.setColorAt(i, tc.set(p[1]).convertSRGBToLinear()); }); levelGroup.add(glowMesh);
  // atmosphere
  scene.background.set(T.fog); scene.fog.color.set(T.fog); scene.fog.density = T.dens;
  hemi.color.set(T.hemi[0]); hemi.groundColor.set(T.hemi[1]); hemi.intensity = T.hemi[2];
  sun.intensity = T.sun ? T.sun[1] : 0; if (T.sun) sun.color.set(T.sun[0]);
  skyGroup.userData.stars.material.opacity = T.weather === 'snow' ? .25 : .7; skyGroup.userData.moon.material.color.set(T.weather === 'ember' ? 0xb08a70 : 0xbfc8d8);
  MAT.weather.color.set(T.weather === 'ember' ? 0xff8a30 : 0xe8eef8); MAT.weather.size = T.weather === 'ember' ? .03 : .05;
  if (flashlight) flashlight.distance = T.dens < .04 ? 44 : 34;
}
const HUGS = { bed: [.98, .5, 1], locker: [1.2, .5, 1], cabinet: [1.18, .45, 0], shelf: [1.22, .5, 1], desk: [1.05, .5, 1], chair: [.9, .28, 0], dumpster: [.95, .6, 1], bench: [1.1, .35, 1], box: [.95, .5, 0], tyres: [1.05, .42, 0], hydrant: [.9, .2, 0], barrel: [1.0, .42, 0] };
const BARCOL = [0x6a4a34, 0x2c3c50, 0x5a2420, 0x3a4630, 0x55504a];
function placeProp(p) {
  const k = p.k, T = THEME; let x = p.x !== undefined ? p.x : wx(p.c), z = p.z !== undefined ? p.z : wx(p.r);
  const nb = () => { navBlock[p.r * W + p.c] = 1; };
  if (k === 'zs') zSpawns.push({ c: p.c, r: p.r, x, z });
  else if (k === 'light') { const dead = p.m === 2, pn = T.panel;
    put('cube', x, WALL_H - .03, z, 0, pn ? 1.32 : 1.3, .08, pn ? 1.32 : .42, 0x1c1c1c);
    const gi = glow(x, WALL_H - .085, z, pn ? 1.16 : 1.12, .04, pn ? 1.16 : .26, dead ? 0x191914 : T.light);
    if (!dead) spot(x, WALL_H - .45, z, T.light, lr(.65, 1) * (pn ? 1.7 : .95), pn ? 13 : 11, p.m === undefined ? (LR() < .55 ? 1 : 0) : p.m, gi); }
  else if (k === 'crate') { addCrate(x, z); nb(); }
  else if (k === 'ammo' || k === 'stim') { addStation(k, x, z); nb(); }
  else if (k === 'car') { const ry = p.ry || 0, s = Math.sin(ry), c = Math.cos(ry);
    put(p.van ? 'van' : 'car', x, p.sink ? -.14 : 0, z, ry, 1, 1, 1, p.col, 0, p.tilt || 0); nb();
    for (const o of [-1.45, 0, 1.45]) colliders.push({ x: x + s * o, z: z + c * o, r: p.van ? 1.05 : .95 });
    if (p.fire) { const gi = glow(x + s * 1.3, 1.0, z + c * 1.3, .8, .35, .8, 0xff7a20, ry); spot(x + s * 1.3, 1.7, z + c * 1.3, 0xff7a28, 1.8, 14, 2, gi); } }
  else if (k === 'pine' || k === 'dtree') { const s = p.s || 1; put(k, x, 0, z, p.ry === undefined ? lr(0, 6) : p.ry, s, s * lr(.9, 1.2), s); colliders.push({ x, z, r: .3 * s }); }
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
  else if (k === 'deb') for (let i = 0, n = 1 + lpick(3); i < n; i++) { const s = lr(.06, .26); put('deb', x + lr(-.5, .5), -s * .1, z + lr(-.5, .5), lr(0, 6), s, s * lr(.4, 1), s * lr(.7, 1.5), T.deb, lr(0, .5), lr(0, .5)); }
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
  const g = new THREE.Group(); g.position.set(x, 0, z);
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
  const show = new THREE.Group(); show.position.set(x, 1.1, z); levelGroup.add(show);
  crateObj = { g, lidP, glow: spot(x, 1.2, z, 0x4aa8ff, .8, 8, 0), show, models: {} };
  for (const id in WEAPONS) { if (id === 'pistol') continue; const m = buildGun(id, false); m.scale.setScalar(1.6); m.rotation.y = Math.PI / 2; m.visible = false; show.add(m); crateObj.models[id] = m; }
  interactables.push({ type: 'crate', x, z, cost: COST.crate, range: 2.4 });
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
const _lc = new THREE.Color();
function updateLights(dt) {
  const cx = camera.position.x, cz = camera.position.z; let dirty = false;
  for (const s of lightSpots) { const pv = s.v;
    if (s.mode === 1) { if (Math.random() < dt * 6) s.v = Math.random() < .3 ? rnd(0, .25) : rnd(.7, 1); }
    else if (s.mode === 2) s.v = .78 + Math.sin(G.time * 13 + s.ph) * .12 + Math.sin(G.time * 31 + s.ph * 2) * .1;
    else s.v = .93 + Math.sin(G.time * 9 + s.ph) * .04;
    if (s.gi >= 0 && Math.abs(pv - s.v) > .02) { glowMesh.setColorAt(s.gi, _lc.copy(s.gc).multiplyScalar(.12 + s.v * .88)); dirty = true; } }
  if (dirty && glowMesh.instanceColor) glowMesh.instanceColor.needsUpdate = true;
  lightT -= dt;
  if (lightT <= 0) { lightT = .2;   // only the nearest few lights are real light sources; the rest are just glowing fixtures
    for (const s of lightSpots) s.d = Math.hypot(s.x - cx, s.z - cz);
    const near = lightSpots.filter(s => s.d < 36).sort((a, b) => a.d - b.d).slice(0, pool.length);
    for (const p of pool) if (p.spot && near.indexOf(p.spot) < 0) { p.spot.pl = -1; p.spot = null; }
    for (const s of near) if (s.pl < 0) { const i = pool.findIndex(p => !p.spot); if (i < 0) break; pool[i].spot = s; s.pl = i; s.a = 0; } }
  for (const p of pool) { const s = p.spot; if (!s) { p.l.intensity = 0; continue; }
    s.a = Math.min(1, s.a + dt * 3); const d = Math.hypot(s.x - cx, s.z - cz);
    p.l.position.set(s.x, s.y, s.z); p.l.color.copy(s.col); p.l.distance = s.range; p.l.intensity = s.base * s.v * s.a * Math.max(0, Math.min(1, (36 - d) / 6)); }
  // sky + weather follow the camera
  skyGroup.position.copy(camera.position);
  const wt = THEME.weather, out = wt && tileAt(Math.floor(cx / TILE), Math.floor(cz / TILE)) !== '.', S = 24;
  const off = wt === 'snow' ? (G.time * 1.7) % 12 : 12 - (G.time * .8) % 12, bx = Math.floor(cx / S) * S, bz = Math.floor(cz / S) * S;
  weatherPts.forEach((p, i) => { p.visible = !!out; if (!out) return; p.position.set(bx + (i & 1) * S + Math.sin(G.time * .3) * .6, -off + ((i >> 2) & 1) * 12, bz + ((i >> 1) & 1) * S); });
}

// ---------------------------------------------------------------- collision
function blocked(x, z, rad) {
  return solid(Math.floor((x - rad) / TILE), Math.floor((z - rad) / TILE)) || solid(Math.floor((x + rad) / TILE), Math.floor((z - rad) / TILE)) ||
         solid(Math.floor((x - rad) / TILE), Math.floor((z + rad) / TILE)) || solid(Math.floor((x + rad) / TILE), Math.floor((z + rad) / TILE));
}
function moveCollide(e, nx, nz, rad) {
  if (!blocked(nx, e.z, rad)) e.x = nx;
  if (!blocked(e.x, nz, rad)) e.z = nz;
  for (const c of colliders) { const dx = e.x - c.x, dz = e.z - c.z, d = Math.hypot(dx, dz), m = rad + c.r;
    if (d < m && d > 1e-4) { const px = c.x + dx / d * m, pz = c.z + dz / d * m; if (!blocked(px, pz, rad)) { e.x = px; e.z = pz; } } }
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
  const SK = [.75, .45];
  GEO.headZ = merged([[sph(.115, 22, 18), M(0, 0, 0, 0, 0, 0, .9, 1.2, 1)], [new THREE.BoxGeometry(.024, .04, .03), M(0, -.008, .112, -.25, 0, 0), SK],
    [sph(.03, 8, 6), M(.103, 0, 0, 0, 0, 0, .35, 1, .7), SK], [sph(.03, 8, 6), M(-.103, 0, 0, 0, 0, 0, .35, 1, .7), SK], [new THREE.BoxGeometry(.11, .016, .02), M(0, .05, .098, .2, 0, 0), SK]]);
  GEO.eyes = merged([[sph(.0125, 8, 6), M(.041, .027, .094)], [sph(.0125, 8, 6), M(-.041, .027, .094)]]);
  GEO.hair = new THREE.SphereGeometry(.119, 14, 8, 0, Math.PI * 2, 0, Math.PI * .42); GEO.hair.scale(.92, 1.2, 1.02);
  GEO.helmet = new THREE.SphereGeometry(.125, 14, 8, 0, Math.PI * 2, 0, Math.PI * .55); GEO.helmet.scale(.98, 1.2, 1.08);
  const B = (w, h, l) => new THREE.BoxGeometry(w, h, l);
  GEO.vest = merged([[B(.43, .36, .28), M(0, .36, 0)], [B(.1, .12, .06), M(-.125, .26, .16)], [B(.1, .12, .06), M(0, .26, .16)], [B(.1, .12, .06), M(.125, .26, .16)], [B(.16, .1, .05), M(.09, .45, .155)],
    [B(.3, .4, .15), M(0, .4, -.21)], [B(.26, .1, .16), M(0, .64, -.2)], [B(.07, .08, .3), M(-.14, .6, 0)], [B(.07, .08, .3), M(.14, .6, 0)], [B(.44, .07, .3), M(0, .12, 0)], [B(.09, .14, .07), M(-.2, .1, .1)], [B(.08, .2, .1), M(.23, .02, 0)]]);

  const bump = bumpTex(), tones = ['#5d6654', '#6a6756', '#4c554e'];
  const skinT = base => canvasTex(256, (g, s) => {
    g.fillStyle = base; g.fillRect(0, 0, s, s); blotch(g, s, 44, '28,34,26', 6, 28, .55); blotch(g, s, 16, '112,114,92', 4, 16, .22); blotch(g, s, 10, '50,30,48', 6, 20, .3);
    veins(g, s, 14, 'rgba(38,28,52,.4)'); for (let i = 0; i < 4; i++) gash(g, Math.random() * s, Math.random() * s, rnd(6, 13)); blotch(g, s, 4, '70,6,4', 8, 24, .6); grainFx(g, s, 22);
  });
  const faceT = base => canvasTex(256, (g, s) => {
    g.fillStyle = base; g.fillRect(0, 0, s, s); blotch(g, s, 40, '28,34,26', 6, 26, .5); blotch(g, s, 12, '50,30,48', 6, 18, .3); veins(g, s, 10, 'rgba(38,28,52,.4)');
    const cx = 64, sh = (x, y, r, c, a) => { const gr = g.createRadialGradient(x, y, 0, x, y, r); gr.addColorStop(0, `rgba(${c},${a})`); gr.addColorStop(1, `rgba(${c},0)`); g.fillStyle = gr; g.fillRect(x - r, y - r, r * 2, r * 2); };
    sh(cx - 24, 146, 17, '16,20,14', .6); sh(cx + 24, 146, 17, '16,20,14', .6); sh(cx, 96, 30, '20,22,16', .25);
    for (const sx of [-17, 17]) { sh(cx + sx, 112, 21, '85,18,14', .45); sh(cx + sx, 112, 15, '4,2,2', 1); sh(cx + sx, 112, 11, '0,0,0', 1); }
    g.strokeStyle = 'rgba(12,10,8,.75)'; g.lineWidth = 3; for (const sx of [-17, 17]) { g.beginPath(); g.moveTo(cx + sx - 13, 100 + (sx > 0 ? -3 : 2)); g.quadraticCurveTo(cx + sx, 94, cx + sx + 13, 100 + (sx > 0 ? 2 : -3)); g.stroke(); }
    g.fillStyle = 'rgba(10,6,5,.85)'; g.beginPath(); g.ellipse(cx - 4, 139, 2.6, 2, 0, 0, 7); g.ellipse(cx + 4, 139, 2.6, 2, 0, 0, 7); g.fill();
    sh(cx, 158, 26, '75,6,4', .55);
    g.fillStyle = '#0d0303'; g.beginPath(); g.ellipse(cx, 156, 17, 9 + Math.random() * 3, rnd(-.12, .12), 0, 7); g.fill();
    g.fillStyle = '#b3aa82'; for (let i = -3; i <= 3; i++) { if (Math.random() < .2) continue; g.fillRect(cx + i * 4.3 - 1.6, 149 + Math.abs(i) * .7, 3.1, rnd(3, 5)); g.fillRect(cx + i * 4.1 - 1.5, 160 - Math.abs(i) * .6, 2.9, rnd(2.5, 4.5)); }
    for (let i = 0; i < 5; i++) { const x = cx + rnd(-14, 14), h = rnd(18, 60), gr = g.createLinearGradient(0, 162, 0, 162 + h); gr.addColorStop(0, 'rgba(70,4,3,.9)'); gr.addColorStop(1, 'rgba(70,4,3,0)'); g.fillStyle = gr; g.fillRect(x, 162, rnd(2, 6), h); }
    gash(g, cx + rnd(-30, 30), rnd(60, 90), rnd(7, 12)); gash(g, rnd(120, 240), rnd(60, 200), rnd(8, 14));
    g.strokeStyle = 'rgba(14,11,8,.8)'; g.lineWidth = 1.2; for (let i = 0; i < 260; i++) { const x = Math.random() * s, y = Math.random() * 46; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-3, 3), y + rnd(4, 14)); g.stroke(); }
    grainFx(g, s, 20);
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
  MAT.dark = new THREE.MeshStandardMaterial({ color: 0x0b0806, roughness: .9 });
  MAT.eye = new THREE.MeshBasicMaterial({ color: 0x7d7a60 });
  MAT.gear = new THREE.MeshStandardMaterial({ color: 0x2c3327, roughness: .9 }); MAT.gearC = [0x4a5a3c, 0x34507a, 0x7a3a30, 0x7a6c38].map(c => new THREE.MeshStandardMaterial({ color: c, roughness: .9 })); MAT.gear2 = new THREE.MeshStandardMaterial({ color: 0x33373a, roughness: .8 });
  MAT.pskin = new THREE.MeshStandardMaterial({ color: 0x9a7a66, roughness: .8 });
  for (const m of [MAT.gear, MAT.gear2, MAT.pskin, MAT.hair].concat(MAT.gearC)) m.color.convertSRGBToLinear();
  MAT.pface = new THREE.MeshStandardMaterial({ map: canvasTex(256, (g, s) => { g.fillStyle = '#93715d'; g.fillRect(0, 0, s, s); blotch(g, s, 20, '70,48,38', 8, 30, .3); const cx = 64;
    for (const sx of [-17, 17]) { g.fillStyle = 'rgba(60,36,28,.5)'; g.beginPath(); g.ellipse(cx + sx, 112, 11, 7, 0, 0, 7); g.fill(); g.fillStyle = '#e4e0d8'; g.beginPath(); g.ellipse(cx + sx, 112, 7, 3.6, 0, 0, 7); g.fill();
      g.fillStyle = '#2a1c12'; g.beginPath(); g.arc(cx + sx, 112, 3.3, 0, 7); g.fill(); g.strokeStyle = '#2a1a10'; g.lineWidth = 3.5; g.beginPath(); g.moveTo(cx + sx - 10, 102 + (sx > 0 ? -1 : 1)); g.lineTo(cx + sx + 10, 102 + (sx > 0 ? 1 : -1)); g.stroke(); }
    g.strokeStyle = 'rgba(50,28,20,.7)'; g.lineWidth = 2; g.beginPath(); g.moveTo(cx - 2, 120); g.lineTo(cx - 5, 138); g.lineTo(cx + 5, 139); g.stroke();
    g.strokeStyle = '#4a2420'; g.lineWidth = 3; g.beginPath(); g.moveTo(cx - 11, 156); g.quadraticCurveTo(cx, 159, cx + 11, 156); g.stroke();
    for (let i = 0; i < 700; i++) { g.fillStyle = 'rgba(30,22,18,.4)'; g.fillRect(cx + rnd(-28, 28), rnd(144, 188), 1.5, 1.5); } blotch(g, s, 6, '20,16,12', 6, 18, .35); grainFx(g, s, 12); }), roughness: .75 });
  // gun + arm materials
  MAT.gMetal = new THREE.MeshStandardMaterial({ map: canvasTex(256, (g, s) => { g.fillStyle = '#2a2d30'; g.fillRect(0, 0, s, s);
    for (let i = 0; i < 500; i++) { g.fillStyle = `rgba(${Math.random() < .5 ? '255,255,255' : '0,0,0'},${rnd(.02, .09)})`; g.fillRect(Math.random() * s, Math.random() * s, rnd(8, 70), 1); }
    blotch(g, s, 20, '110,112,115', 2, 9, .3); blotch(g, s, 14, '0,0,0', 8, 30, .35); grainFx(g, s, 14); }), metalness: .85, roughness: .4, envMapIntensity: .9 });
  MAT.gPoly = new THREE.MeshStandardMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#1b1c1d'; g.fillRect(0, 0, s, s); blotch(g, s, 20, '60,60,58', 2, 8, .18); grainFx(g, s, 22); }), bumpMap: bump, bumpScale: .0015, metalness: .1, roughness: .72, envMapIntensity: .5 });
  MAT.gWood = new THREE.MeshStandardMaterial({ map: canvasTex(256, (g, s) => { g.fillStyle = '#4a2e18'; g.fillRect(0, 0, s, s);
    for (let i = 0; i < 150; i++) { g.fillStyle = `rgba(${rnd(10, 110) | 0},${rnd(8, 60) | 0},12,.3)`; g.fillRect(0, Math.random() * s, s, rnd(1, 3)); } blotch(g, s, 10, '15,8,4', 10, 40, .4); grainFx(g, s, 16); }), roughness: .45, metalness: 0, envMapIntensity: .6 });
  MAT.gSleeve = new THREE.MeshStandardMaterial({ map: canvasTex(256, (g, s) => { g.fillStyle = '#3b4230'; g.fillRect(0, 0, s, s); blotch(g, s, 30, '28,32,22', 12, 40, .8); blotch(g, s, 22, '70,66,46', 10, 30, .55); blotch(g, s, 16, '18,18,14', 8, 26, .7); weave(g, s); grainFx(g, s, 26); }), bumpMap: bump, bumpScale: .004, roughness: 1, envMapIntensity: .1 });
  MAT.gGlove = new THREE.MeshStandardMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#141414'; g.fillRect(0, 0, s, s); blotch(g, s, 20, '50,48,44', 3, 12, .25); grainFx(g, s, 26); }), bumpMap: bump, bumpScale: .002, roughness: .6, envMapIntensity: .4 });
  MAT.gGlass = new THREE.MeshStandardMaterial({ color: 0x3a6a90, transparent: true, opacity: .22, metalness: 1, roughness: .05, depthWrite: false });
  MAT.gDark = new THREE.MeshStandardMaterial({ color: 0x050505, roughness: .9 });
}
function buildHumanoid(o) {
  const g = new THREE.Group(), body = new THREE.Group(); g.add(body);
  const mk = (geo, mat, par, x, y, z) => { const m = new THREE.Mesh(geo, mat); m.position.set(x || 0, y || 0, z || 0); m.castShadow = true; par.add(m); return m; };
  const legs = [], shins = [], arms = [], fore = [];
  for (const s of [-1, 1]) {
    const leg = new THREE.Group(); leg.position.set(s * .1, .92, 0); body.add(leg); mk(GEO.thigh, o.pants, leg);
    const shin = new THREE.Group(); shin.position.y = -.46; leg.add(shin); mk(GEO.shin, o.pants, shin); mk(GEO.foot, o.shoe, shin);
    legs.push(leg); shins.push(shin);
  }
  const torso = new THREE.Group(); torso.position.y = .92; body.add(torso); mk(GEO.torso, o.cloth, torso);
  const head = new THREE.Group(); head.position.set(0, .74, .015); torso.add(head);
  const skull = mk(GEO.headZ, o.face, head, 0, .135, 0); skull.userData.head = true;
  if (o.player) { mk(GEO.helmet, MAT.gear2, head, 0, .15, 0); mk(GEO.vest, MAT.gear2, torso); }
  else { const e = mk(GEO.eyes, MAT.eye, head, 0, .135, 0); e.castShadow = false; e.userData.head = true; if (o.hair) mk(GEO.hair, MAT.hair, head, 0, .138, 0).userData.head = true; }
  for (const s of [-1, 1]) {
    const arm = new THREE.Group(); arm.position.set(s * .235, .56, 0); torso.add(arm); mk(GEO.upper, o.cloth, arm);
    const f = new THREE.Group(); f.position.y = -.32; arm.add(f); mk(GEO.fore, o.skin, f); mk(GEO.hand, o.skin, f).scale.x = s;
    arms.push(arm); fore.push(f);
  }
  return { g, body, torso, head, skull, legs, shins, arms, fore, ph: 0, lastAtk: 0 };
}
function makeZombieView(z) {
  const R = seeded(z.id * 7919 + 13), tone = (R() * 3) | 0;
  const v = buildHumanoid({ skin: MAT.zSkin[tone], face: MAT.zFace[tone], cloth: MAT.zShirt[(R() * 6) | 0], pants: MAT.zPants[(R() * 3) | 0], shoe: R() < .4 ? MAT.zSkin[tone] : MAT.dark, hair: R() < .6 });
  v.limp = R() < .3 ? 1 : 0; v.armDown = R() < .25 ? (R() < .5 ? 0 : 1) : -1; v.tw = R() * 10;
  if (R() < .16) v.fore[R() < .5 ? 0 : 1].visible = false;
  const sc = .94 + R() * .14; v.g.scale.set(sc * (.92 + R() * .2), sc, sc * (.95 + R() * .15));
  v.g.traverse(o => { if (o.isMesh) o.userData.zr = z; });
  v.g.position.set(z.x, -1.9, z.z); zGroup.add(v.g); z.view = v;
}
function makePlayerView(p) {
  const v = buildHumanoid({ skin: MAT.gGlove, face: MAT.pface, cloth: MAT.gearC[p.ci | 0] || MAT.gear, pants: MAT.gear2, shoe: MAT.dark, player: true });
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
  lmg:     { rl: .28, hg: .26, hgR: .03,  brl: .22, brlR: .011,  stock: 'solid', stockL: .22, mag: 'box',      optic: 'iron', bipod: true }
};
function buildGun(id, withArms) {
  const P = {}, add = (k, geo, m) => { (P[k] = P[k] || []).push([geo, m]); };
  const bx = (k, w, h, l, x, y, z, rx, ry, rz) => add(k, new THREE.BoxGeometry(w, h, l), M(x, y, z, rx, ry, rz));
  const cz = (k, rBack, rFront, len, x, y, z, n, open) => add(k, new THREE.CylinderGeometry(rBack, rFront, len, n || 14, 1, !!open), M(x, y, z, Math.PI / 2, 0, 0));
  const sp = (k, r, x, y, z, sx, sy, sz) => add(k, new THREE.SphereGeometry(r, 10, 8), M(x, y, z, 0, 0, 0, sx, sy, sz));
  const seg = (k, rA, rB, A, B, n) => { const a = V3(A[0], A[1], A[2]), b = V3(B[0], B[1], B[2]), d = b.clone().sub(a), len = d.length();
    const q = new THREE.Quaternion().setFromUnitVectors(V3(0, 1, 0), d.normalize()); add(k, new THREE.CylinderGeometry(rB, rA, len, n || 10), new THREE.Matrix4().compose(a.add(b).multiplyScalar(.5), q, V3(1, 1, 1))); };
  let muzzleZ, sightY, grip, fore = null, adsZ = .1, by = .012;
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
  } else {
    const d = GUNDEF[id], rl = d.rl, zf = -rl / 2, zb = rl / 2, hz = zf - d.hg / 2, bl = d.hg + d.brl;
    bx('Metal', .044, .048, rl, 0, .012, 0); bx('Metal', .04, .036, rl * .78, 0, -.028, rl * .08);
    bx('Dark', .002, .016, .05, .0225, .016, -.02); bx('Metal', .028, .008, .02, 0, .03, zb - .005); bx('Metal', .006, .01, .012, .024, .004, .02);
    if (!d.pump) { bx('Metal', .02, .007, rl, 0, .0395, 0); for (let i = 0; i < Math.floor(rl / .012); i++) bx('Metal', .022, .004, .006, 0, .045, zf + .006 + i * .012); }
    bx('Metal', .01, .004, .065, 0, -.056, zb - .085); bx('Metal', .004, .02, .006, 0, -.044, zb - .085, -.3);
    if (d.stock === 'wood') grip = [0, -.045, zb + .03]; else { bx('Poly', .03, .095, .04, 0, -.088, zb - .035, .33); grip = [0, -.088, zb - .035]; }
    cz('Metal', d.brlR, d.brlR, bl, 0, by, zf - bl / 2, 12); muzzleZ = zf - bl; cz('Dark', d.brlR * .6, d.brlR * .6, .01, 0, by, muzzleZ + .004, 8);
    if (d.pump) {
      cz('Metal', .011, .011, d.hg + .1, 0, -.014, hz - .05); cz('Wood', .025, .025, .14, 0, -.012, hz - .02, 12);
      for (let i = 0; i < 6; i++) bx('Dark', .051, .03, .003, 0, -.014, hz - .075 + i * .022);
      bx('Metal', .008, .006, bl, 0, .036, zf - bl / 2); sp('Metal', .004, 0, .043, muzzleZ + .015); sightY = .05; fore = [0, -.037, hz - .02];
    } else {
      cz('Poly', d.hgR, d.hgR * .94, d.hg, 0, by, hz, 8); bx('Metal', .018, .007, d.hg, 0, by + d.hgR + .001, hz);
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
    const mz = zf + .055;
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
  updateLights(dt);
}
function bloodDecal(x, z) { const m = bloods[bloodI = (bloodI + 1) % bloods.length]; m.position.set(x, .015 + bloodI * .0004, z); m.rotation.y = rnd(0, 6); const s = rnd(.6, 1.3); m.scale.set(s, 1, s); m.visible = true; }

// ---------------------------------------------------------------- players
function newPlayer(id, name) {
  return { id, name: name || 'Survivor', x: SPAWN.x + rnd(-1.5, 1.5), y: 0, z: SPAWN.z + rnd(-1.5, 1.5), yaw: 0, pitch: 0, hp: 100, maxHp: 100, down: false,
    points: 500, kills: 0, wid: 'pistol', fireSeq: 0, lastHurt: -99, view: null, ci: 0 };
}
function removePlayer(id) { const p = players[id]; if (!p) return; if (p.view) scene.remove(p.view.g); delete players[id]; }
const curW = () => L.weapons[L.wi];
function giveWeapon(id) {
  const d = WEAPONS[id], w = { id, ammo: d.mag, reserve: d.reserve };
  if (L.weapons.length < 2) { L.weapons.push(w); L.wi = L.weapons.length - 1; } else L.weapons[L.wi] = w;
  L.switchT = .4; L.reloadT = 0; me.wid = id;
}
function switchWeapon(i) { if (i === L.wi || !L.weapons[i] || me.down) return; L.wi = i; L.switchT = .35; L.reloadT = 0; me.wid = curW().id; sNoise(2000, .05, .15); }
function startReload() { const w = curW(), d = WEAPONS[w.id]; if (L.reloadT > 0 || w.ammo >= d.mag || w.reserve <= 0) return; L.reloadT = d.reload; sNoise(2500, .06, .25); setTimeout(() => sNoise(1800, .08, .3), d.reload * 700); }

const _v = new THREE.Vector3(), _d = new THREE.Vector3(), _q = new THREE.Quaternion();
function castShot(dir, far) {
  raycaster.set(camera.position, dir); raycaster.far = far;
  const hits = raycaster.intersectObjects(shootables, true);
  for (const h of hits) { const z = h.object.userData.zr; if (z && (z.dead || z.rise < .5)) continue; return h; }
  return null;
}
function fire() {
  const w = curW(), d = WEAPONS[w.id]; w.ammo--; L.fireT = 60 / d.rpm; L.fired = true; L.kick = 1;
  const moving = keys.KeyW || keys.KeyA || keys.KeyS || keys.KeyD;
  const sp = d.spread * (1 - L.ads * .65) * (moving ? 1.6 : 1) + (d.pellets > 1 ? 0 : (1 - L.ads) * .006);
  let anyHit = false;
  for (let i = 0; i < d.pellets; i++) {
    camera.getWorldDirection(_d); _d.x += rnd(-sp, sp); _d.y += rnd(-sp, sp); _d.z += rnd(-sp, sp); _d.normalize();
    const h = castShot(_d, 120); if (!h) continue;
    const z = h.object.userData.zr;
    if (z) { const head = !!h.object.userData.head; anyHit = true; burst(h.point, head ? 14 : 8, [.4, .02, .02], 1.8); dealHit(z.id, d.dmg * (head ? 2.5 : 1), head); }
    else { burst(h.point, 5, [.5, .45, .35], 1.4);
      if (h.face) { const m = holes[holeI = (holeI + 1) % holes.length]; _v.copy(h.face.normal); if (h.object.rotation.y) _v.applyEuler(h.object.rotation);
        m.position.copy(h.point).addScaledVector(_v, .012); m.lookAt(_v.add(m.position)); m.visible = true; } }
  }
  if (anyHit) { L.hitFx = 1; sTone(1400, .04, .12, 'square'); }
  me.pitch = Math.min(1.5, me.pitch + d.kick * (1 - L.ads * .3)); me.yaw += rnd(-1, 1) * d.kick * .35;
  me.fireSeq++; sShot(w.id, 1);
  muzzleLight.intensity = 3.2; muzzleFlash.visible = true; muzzleFlash.rotation.z = rnd(0, 6); muzzleFlash.scale.setScalar(rnd(.8, 1.4) * (w.id === 'shotgun' ? 1.6 : 1));
  setTimeout(() => { muzzleLight.intensity = 0; muzzleFlash.visible = false; }, 45);
  if (w.ammo === 0 && w.reserve > 0) setTimeout(startReload, 250);
}
const KNIFE_T = .48, _up = new THREE.Vector3(0, 1, 0);
function melee() {
  if (L.meleeT > 0 || !me || me.down || L.switchT > 0) return; L.meleeT = KNIFE_T; L.meleeHit = true; sNoise(1500, .1, .28, 'bandpass'); sNoise(700, .16, .18, 'highpass');
}
function knifeHit() {   // the slash lands part-way through the swing and covers a small arc
  for (const a of [0, -.2, .2, -.4, .4]) { camera.getWorldDirection(_d); if (a) _d.applyAxisAngle(_up, a); const h = castShot(_d, 2.7);
    if (h && h.object.userData.zr) { burst(h.point, 16, [.4, .02, .02], 2.2); dealHit(h.object.userData.zr.id, 160, false, true); L.hitFx = 1; sNoise(200, .12, .6); sTone(90, .1, .4, 'sine', 0, 50); return; } }
}
function dealHit(zid, dmg, head, knife) { if (G.host) hostHit(G.myId, zid, dmg, head, knife); else netSend({ t: 'hit', z: zid, d: Math.round(dmg), h: head ? 1 : 0, k: knife ? 1 : 0 }); }

// ---------------------------------------------------------------- interaction
function nearestInteractable() {
  if (!me || me.down) return null; let best = null, bd = 1e9;
  for (const it of interactables) { if (it.type === 'door' && doorOpen[it.id]) continue; const d = Math.hypot(it.x - me.x, it.z - me.z); if (d < it.range && d < bd) { bd = d; best = it; } }
  return best;
}
function promptFor(it) {
  if (it.type === 'door') return `Press <b>E</b> to clear the barricade to ${DOORS[it.id].name} &nbsp;[${it.cost}]`;
  if (it.type === 'crate') return L.crateT > 0 ? '' : `Press <b>E</b> to open the Mystery Crate — random weapon &nbsp;[${it.cost}]`;
  if (it.type === 'ammo') return `Press <b>E</b> to restock ammo &nbsp;[${it.cost}]`;
  return me.maxHp > 100 ? 'Field Stim already taken' : `Press <b>E</b> for Field Stim — double health &nbsp;[${it.cost}]`;
}
function requestBuy(it) {
  if (it.type === 'crate' && L.crateT > 0) return;
  if (it.type === 'stim' && me.maxHp > 100) return;
  if (me.points < it.cost) { sTone(140, .18, .25, 'square'); return; }
  const m = { t: 'buy', k: it.type, i: it.id || '', own: L.weapons.map(w => w.id) };
  if (G.host) hostBuy(G.myId, m); else netSend(m);
}
function hostBuy(pid, m) {
  const p = players[pid]; if (!p || p.down) return; let w = null;
  if (m.k === 'door') { const d = DOORS[m.i]; if (!d || doorOpen[m.i] || p.points < d.cost) return; p.points -= d.cost; openDoor(m.i); }
  else if (m.k === 'crate') { if (p.points < COST.crate) return; p.points -= COST.crate; const own = m.own || []; const pool = Object.keys(WEAPONS).filter(k => k !== 'pistol' && own.indexOf(k) < 0); w = pool[(Math.random() * pool.length) | 0]; }
  else if (m.k === 'ammo') { if (p.points < COST.ammo) return; p.points -= COST.ammo; }
  else if (m.k === 'stim') { if (p.points < COST.stim || p.maxHp > 100) return; p.points -= COST.stim; p.maxHp = 200; p.hp = 200; }
  else return;
  const ok = { t: 'ok', k: m.k, i: m.i, w };
  if (pid === G.myId) onBuyOk(ok); else if (Net.conns[pid]) Net.conns[pid].send(ok);
}
function onBuyOk(m) {
  sTone(660, .1, .2, 'triangle'); sTone(990, .16, .2, 'triangle', .09);
  if (m.k === 'crate') { L.crateT = 3.4; L.crateW = m.w; [392, 494, 587, 784, 587, 784, 988].forEach((f, i) => sTone(f, .22, .12, 'triangle', .2 + i * .38)); }
  else if (m.k === 'ammo') { for (const w of L.weapons) { w.reserve = WEAPONS[w.id].reserve; } showMsg('AMMO RESTOCKED', 1.5); }
  else if (m.k === 'stim') showMsg('FIELD STIM', 1.5);
}
function onEvent(k) {
  if (k === 'ammo') { for (const w of L.weapons) { w.reserve = WEAPONS[w.id].reserve; w.ammo = WEAPONS[w.id].mag; } showMsg('RESUPPLY', 2); }
  if (k === 'insta') showMsg('OVERKILL', 2);
  if (k === 'nuke') { showMsg('PURGE', 2); sNoise(120, 1.4, 1); }
  if (k === 'pick') { sTone(520, .15, .2, 'triangle'); sTone(780, .25, .2, 'triangle', .1); }
}
function broadcast(m) { for (const id in Net.conns) { try { Net.conns[id].send(m); } catch (e) {} } }
function hostEvent(k) { onEvent(k); broadcast({ t: 'ev', k }); }
function hostSay(s) { showMsg(s, 2.5); broadcast({ t: 'msg', s }); }
function dropClient(id) { const c = Net.conns[id], p = players[id]; if (c) { delete Net.conns[id]; try { c.close(); } catch (e) {} } if (p && id !== G.myId) { hostSay(p.name.toUpperCase() + ' LEFT'); removePlayer(id); flowT = 0; } }

// ---------------------------------------------------------------- host simulation
function buildFlow() {
  flow.fill(9999); const q = [];
  for (const id in players) { const p = players[id]; if (p.down) continue; const c = Math.floor(p.x / TILE), r = Math.floor(p.z / TILE); if (solid(c, r)) continue; const i = r * W + c; if (flow[i] !== 0) { flow[i] = 0; q.push(i); } }
  for (let h = 0; h < q.length; h++) { const i = q[h], c = i % W, r = (i / W) | 0, d = flow[i] + 1;
    for (const [dc, dr] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) { const nc = c + dc, nr = r + dr; if (navSolid(nc, nr)) continue; const ni = nr * W + nc; if (flow[ni] > d) { flow[ni] = d; q.push(ni); } } }
}
const N8 = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
function spawnZombie() {
  const ok = zSpawns.filter(s => flow[s.r * W + s.c] < 9000); if (!ok.length) return false;
  const fd = s => flow[s.r * W + s.c]; let far = ok.filter(s => fd(s) >= 3 && fd(s) <= 13); if (!far.length) far = ok.filter(s => fd(s) >= 3); const s = (far.length ? far : ok)[(Math.random() * (far.length ? far.length : ok.length)) | 0];
  const r = G.round, runner = r >= 4 && Math.random() < Math.min(.12 + r * .04, .7);
  const z = { id: zSeq++, x: s.x + rnd(-1, 1), z: s.z + rnd(-1, 1), rot: rnd(0, 6), rise: 0, atk: 0, atkT: .5, dead: false,
    hp: r < 10 ? 100 + (r - 1) * 55 : 595 * Math.pow(1.1, r - 9), speed: Math.min(5.8, (1.5 + Math.min(r, 12) * .16 + Math.random() * .5) * (runner ? 1.6 : 1)) };
  zombies.push(z); zById[z.id] = z; makeZombieView(z); return true;
}
function killZombie(z, head, silent) {
  const i = zombies.indexOf(z); if (i >= 0) zombies.splice(i, 1); delete zById[z.id]; z.dead = true;
  const v = z.view; if (!v) return;
  if (head) { v.head.traverse(o => { if (o.isMesh) o.visible = false; }); _v.set(z.x, 1.6, z.z); burst(_v, 26, [.4, .02, .02], 2.6); }
  bloodDecal(z.x, z.z); corpses.push({ v, t: 0 });
  if (!silent) sGroan(distVol(z.x, z.z, 26) * .8);
}
function hostHit(pid, zid, dmg, head, knife) {
  const z = zById[zid], p = players[pid]; if (!z || !p) return;
  z.hp -= G.insta > 0 ? 1e9 : dmg; p.points += 10;
  if (z.hp <= 0) {
    p.points += knife ? 120 : head ? 90 : 50; p.kills++;
    if (drops.length < 2 && Math.random() < .045) drops.push({ id: dropSeq++, type: ['ammo', 'insta', 'nuke'][(Math.random() * 3) | 0], x: z.x, z: z.z, t: 25 });
    killZombie(z, head);
  }
}
function damagePlayer(p, d) { if (p.down) return; p.hp -= d; p.lastHurt = G.time; if (p.hp <= 0) { p.hp = 0; p.down = true; flowT = 0; } }
function startRound() {
  G.round++; G.state = 'wave'; const n = Object.keys(players).length;
  G.toSpawn = Math.round((5 + G.round * 2.6) * (1 + .55 * (n - 1))); G.spawnT = 1.5;
  for (const id in players) { const p = players[id]; if (p.down) { p.down = false; p.hp = p.maxHp; } }
}
function hostUpdate(dt) {
  if (G.over) return;
  flowT -= dt; if (flowT <= 0) { flowT = .25; buildFlow(); }
  const all = Object.values(players), alive = all.filter(p => !p.down);
  if (all.length && !alive.length) { G.over = true; G.state = 'over'; sendSnapshot(); gameOver(); return; }
  if (G.insta > 0) G.insta -= dt;
  if (G.state === 'inter') { G.interT -= dt; if (G.interT <= 0) startRound(); }
  else {
    G.spawnT -= dt;
    if (G.toSpawn > 0 && G.spawnT <= 0 && zombies.length < MAX_ALIVE + 5 * (all.length - 1)) { if (spawnZombie()) G.toSpawn--; G.spawnT = Math.max(.35, 2 - G.round * .12); }
    if (G.toSpawn <= 0 && !zombies.length) { G.state = 'inter'; G.interT = 9; }
  }
  for (const z of zombies) {
    if (z.rise < 1) { z.rise = Math.min(1, z.rise + dt / 1.5); continue; }
    let tp = null, td = 1e9; for (const p of alive) { const d = Math.hypot(p.x - z.x, p.z - z.z); if (d < td) { td = d; tp = p; } }
    if (!tp) continue;
    let gx = tp.x, gz = tp.z; const c = Math.floor(z.x / TILE), r = Math.floor(z.z / TILE), here = flow[r * W + c];
    if (here > 1 && here < 9000) { let best = here, bc = c, br = r;
      for (const [dc, dr] of N8) { const nc = c + dc, nr = r + dr; if (navSolid(nc, nr)) continue; if (dc && dr && (navSolid(c + dc, r) || navSolid(c, r + dr))) continue;
        const d = flow[nr * W + nc] + (dc && dr ? .4 : 0); if (d < best) { best = d; bc = nc; br = nr; } }
      gx = wx(bc); gz = wx(br); }
    let dx = gx - z.x, dz = gz - z.z; const dl = Math.hypot(dx, dz) || 1; dx /= dl; dz /= dl;
    z.rot = lerpAngle(z.rot, Math.atan2(td < 2.5 ? tp.x - z.x : dx, td < 2.5 ? tp.z - z.z : dz), dt * 8);
    for (const o of zombies) { if (o === z) continue; const ox = z.x - o.x, oz = z.z - o.z, d2 = ox * ox + oz * oz; if (d2 < .5 && d2 > 1e-4) { const d = Math.sqrt(d2); dx += ox / d * (.72 - d) * 2.5; dz += oz / d * (.72 - d) * 2.5; } }
    if (td > .9) moveCollide(z, z.x + dx * z.speed * dt, z.z + dz * z.speed * dt, .32);
    z.atkT -= dt; if (z.atk > 0) z.atk -= dt;
    if (td < 1.3 && z.atkT <= 0 && tp.y < 1.1) { z.atkT = 1.1; z.atk = .45; damagePlayer(tp, 34); }
  }
  for (const p of all) if (!p.down && p.hp < p.maxHp && G.time - p.lastHurt > 5) p.hp = Math.min(p.maxHp, p.hp + 30 * dt);
  for (let i = drops.length - 1; i >= 0; i--) { const d = drops[i]; d.t -= dt; let got = false;
    for (const p of alive) if (Math.hypot(p.x - d.x, p.z - d.z) < 1.2) got = true;
    if (got) { hostEvent('pick'); if (d.type === 'insta') G.insta = 20;
      if (d.type === 'nuke') { for (const z of zombies.slice()) killZombie(z, false, true); for (const p of all) p.points += 400; }
      hostEvent(d.type); }
    if (got || d.t <= 0) drops.splice(i, 1); }
  Net.sendT -= dt; if (Net.sendT <= 0) { Net.sendT = 1 / 14; sendSnapshot(); const now = performance.now(); for (const id in Net.conns) if (now - (Net.conns[id].seen || now) > 12000) dropClient(id); }
}
const r2 = v => Math.round(v * 100) / 100;
function sendSnapshot() {
  if (!Object.keys(Net.conns).length) return;
  broadcast({ t: 's', r: G.round, st: G.state, it: r2(G.interT), left: G.toSpawn + zombies.length, insta: r2(Math.max(0, G.insta)), doors: Object.keys(doorOpen).join(''),
    P: Object.values(players).map(p => [p.id, p.name, r2(p.x), r2(p.y), r2(p.z), r2(p.yaw), r2(p.pitch), Math.round(p.hp), p.maxHp, p.down ? 1 : 0, p.points, p.kills, p.wid, p.fireSeq, p.ci | 0]),
    Z: zombies.map(z => [z.id, r2(z.x), r2(z.z), r2(z.rot), r2(z.rise), z.atk > 0 ? 1 : 0]), D: drops.map(d => [d.id, d.type, r2(d.x), r2(d.z)]) });
}
function hostRecv(pid, m) {
  if (!m || !m.t) return;
  if (m.t === 'hello') { const c = Net.conns[pid];
    if (!players[pid]) {
      if (Object.keys(players).length >= 4 || G.over) { if (c) { try { c.send({ t: 'full' }); } catch (e) {} setTimeout(() => { try { c.close(); } catch (e) {} }, 600); } delete Net.conns[pid]; return; }
      const p = players[pid] = newPlayer(pid, String(m.name || 'Survivor').slice(0, 14));
      p.ci = [1, 2, 3, 0].find(i => !Object.values(players).some(q => q !== p && q.ci === i)) || 0; hostSay(p.name.toUpperCase() + ' JOINED'); }
    if (c) c.send({ t: 'w', map: MAPID, doors: Object.keys(doorOpen).join('') }); return; }
  const p = players[pid]; if (!p) return;
  if (m.t === 'p') { p.x = +m.a[0] || 0; p.y = +m.a[1] || 0; p.z = +m.a[2] || 0; p.yaw = +m.a[3] || 0; p.pitch = +m.a[4] || 0; if (WEAPONS[m.a[5]]) p.wid = m.a[5]; p.fireSeq = m.a[6] | 0; }
  else if (m.t === 'hit') hostHit(pid, m.z, Math.min(600, +m.d || 0), !!m.h, !!m.k);
  else if (m.t === 'buy') hostBuy(pid, m);
}

// ---------------------------------------------------------------- client
function clientRecv(m) {
  if (!m || !m.t) return;
  if (m.t === 'ok') return onBuyOk(m);
  if (m.t === 'ev') return onEvent(m.k);
  if (m.t === 'msg') return showMsg(String(m.s).slice(0, 40), 2.5);
  if (m.t !== 's') return;
  G.round = m.r; G.state = m.st; G.interT = m.it; G.left = m.left; G.insta = m.insta;
  for (const ch of m.doors) if (!doorOpen[ch]) openDoor(ch);
  const seenP = {};
  for (const a of m.P) { const id = a[0]; seenP[id] = 1; let p = players[id]; if (!p) { p = players[id] = newPlayer(id, a[1]); }
    p.name = a[1]; p.ci = a[14] | 0; p.hp = a[7]; p.maxHp = a[8]; p.down = !!a[9]; p.points = a[10]; p.kills = a[11];
    if (id !== G.myId) { p.x = a[2]; p.y = a[3]; p.z = a[4]; p.yaw = a[5]; p.pitch = a[6]; p.wid = a[12]; p.fireSeq = a[13]; } }
  for (const id in players) if (!seenP[id] && id !== G.myId) removePlayer(id);
  const seenZ = {};
  for (const a of m.Z) { let z = zById[a[0]]; seenZ[a[0]] = 1;
    if (!z) { z = { id: a[0], x: a[1], z: a[2], rot: a[3], rise: a[4], atk: 0, dead: false }; zombies.push(z); zById[z.id] = z; makeZombieView(z); }
    z.x = a[1]; z.z = a[2]; z.rot = a[3]; z.rise = a[4]; z.atk = a[5] ? .3 : 0; }
  for (const z of zombies.slice()) if (!seenZ[z.id]) killZombie(z, false);
  drops.length = 0; for (const a of m.D) drops.push({ id: a[0], type: a[1], x: a[2], z: a[3] });
  if (m.st === 'over' && !G.over) { G.over = true; gameOver(); }
}
function netSend(m) { if (Net.conn && Net.conn.open) Net.conn.send(m); }
function hostLost() {
  if (G.over) return; G.over = true; document.exitPointerLock && document.exitPointerLock();
  $('overtitle').textContent = 'DISCONNECTED'; $('overtext').textContent = 'The connection to the host was lost.'; $('over').style.display = 'flex';
}
function clientUpdate(dt) {
  if (Net.lastRecv && performance.now() - Net.lastRecv > 9000) hostLost();
  Net.sendT -= dt; if (Net.sendT <= 0) { Net.sendT = 1 / 15; netSend({ t: 'p', a: [r2(me.x), r2(me.y), r2(me.z), r2(me.yaw), r2(me.pitch), me.wid, me.fireSeq] }); }
}

// ---------------------------------------------------------------- local player
function updateLocal(dt) {
  if (me.hp < L.lastHp - .5) { L.hurt = 1; sNoise(180, .2, .7); sTone(90, .25, .5, 'sawtooth', 0, 50); } L.lastHp = me.hp;
  if (me.down) { L.wasDown = true; camera.position.set(me.x, .4, me.z); camera.rotation.set(-.2, me.yaw, .5); return; }
  if (L.wasDown) { L.wasDown = false; me.x = SPAWN.x; me.z = SPAWN.z; for (const w of L.weapons) w.ammo = WEAPONS[w.id].mag; showMsg('BACK ON YOUR FEET', 2); }
  const f = (keys.KeyW ? 1 : 0) - (keys.KeyS ? 1 : 0), s = (keys.KeyD ? 1 : 0) - (keys.KeyA ? 1 : 0);
  L.sprint = !!(keys.ShiftLeft || keys.ShiftRight) && f > 0 && !mouse.r;
  const sp = mouse.r ? 2.4 : L.sprint ? 6.4 : 4.1, len = Math.hypot(f, s) || 1, sin = Math.sin(me.yaw), cos = Math.cos(me.yaw);
  moveCollide(me, me.x + (-sin * f + cos * s) / len * sp * dt, me.z + (-cos * f - sin * s) / len * sp * dt, .38);
  if (keys.Space && L.onGround) { L.vy = 5; L.onGround = false; }
  L.vy -= 14 * dt; me.y += L.vy * dt; if (me.y <= 0) { me.y = 0; L.vy = 0; L.onGround = true; }
  const moving = (f || s) && L.onGround;
  if (moving) { L.bob += dt * (L.sprint ? 13 : 9); if (Math.floor(L.bob / Math.PI) !== L.stepPh) { L.stepPh = Math.floor(L.bob / Math.PI); sNoise(140, .07, L.sprint ? .22 : .13); } }
  // weapon
  const w = curW(), d = WEAPONS[w.id]; L.fireT -= dt; if (L.switchT > 0) L.switchT -= dt; if (L.meleeT > 0) { L.meleeT -= dt; if (L.meleeHit && L.meleeT < KNIFE_T * .62) { L.meleeHit = false; knifeHit(); } }
  if (L.reloadT > 0) { L.reloadT -= dt; if (L.reloadT <= 0) { const n = Math.min(d.mag - w.ammo, w.reserve); w.ammo += n; w.reserve -= n; } }
  if (mouse.l && document.pointerLockElement && L.fireT <= 0 && L.reloadT <= 0 && L.switchT <= 0 && L.meleeT <= 0 && (d.auto || !L.fired)) {
    if (w.ammo > 0) fire(); else { L.fired = true; sTone(900, .03, .15, 'square'); startReload(); } }
  if (!mouse.l) L.fired = false;
  const wantAds = mouse.r && L.reloadT <= 0 && !L.sprint ? 1 : 0; L.ads += (wantAds - L.ads) * Math.min(1, dt * 14);
  L.kick = Math.max(0, L.kick - dt * 9); L.hitFx = Math.max(0, L.hitFx - dt * 5); L.hurt = Math.max(0, L.hurt - dt * 1.2);
  // crate animation
  if (L.crateT > 0) { L.crateT -= dt; const c = crateObj, k = 3.4 - L.crateT; c.lidP.rotation.x = -Math.min(1, k * 3) * 1.3; c.glow.base = 1.7;
    const ids = Object.keys(c.models), showId = L.crateT < .9 ? L.crateW : ids[Math.floor(k * 8) % ids.length];
    for (const id of ids) c.models[id].visible = id === showId; c.show.position.y = 1 + Math.min(.5, k * .4); c.show.rotation.y += dt * 1.5;
    if (L.crateT <= 0) { for (const id of ids) c.models[id].visible = false; c.lidP.rotation.x = 0; c.glow.base = .8; giveWeapon(L.crateW); showMsg(WEAPONS[L.crateW].name.toUpperCase(), 2); sNoise(2200, .08, .3); } }
  // camera
  const bobY = moving ? Math.sin(L.bob * 2) * (L.sprint ? .055 : .03) * (1 - L.ads * .7) : 0;
  camera.position.set(me.x, EYE + me.y + bobY, me.z); camera.rotation.set(me.pitch, me.yaw, moving ? Math.sin(L.bob) * .006 : 0);
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
  knife.visible = L.meleeT > 0;
  if (knife.visible) { const t = 1 - L.meleeT / KNIFE_T, e = t * t * (3 - 2 * t), sw = Math.sin(t * Math.PI);
    knife.position.set(.3 - .56 * e, -.03 - .13 * e + .06 * sw, -.36 - .13 * sw); knife.rotation.set(.45 - .7 * e, .15 + 1.15 * e, -.7 + 1.3 * e); }
  muzzleFlash.position.set(0, gv.userData.muzzleY, gv.userData.muzzleZ - .06);
  flashlight.intensity = L.flash ? 2.3 * (Math.random() < .004 ? .3 : 1) : 0; wLight.intensity = L.flash ? 1.4 : .4;
}

// ---------------------------------------------------------------- views
const dropMeshes = {};
function updateViews(dt) {
  const k = Math.min(1, dt * 12);
  for (const z of zombies) { const v = z.view, g = v.g; const ox = g.position.x, oz = g.position.z;
    g.position.x += (z.x - ox) * k; g.position.z += (z.z - oz) * k; g.position.y = (Math.min(1, z.rise) - 1) * 1.9;
    g.rotation.y = lerpAngle(g.rotation.y, z.rot, dt * 10);
    const mv = Math.hypot(g.position.x - ox, g.position.z - oz); v.ph += mv * 3.4; const ph = v.ph, t = G.time + v.tw;
    v.legs[0].rotation.x = Math.sin(ph) * .65; v.legs[1].rotation.x = -Math.sin(ph) * (v.limp ? .25 : .65);
    v.shins[0].rotation.x = Math.max(0, -Math.sin(ph)) * .9 + .1; v.shins[1].rotation.x = Math.max(0, Math.sin(ph)) * .9 + .1;
    const atk = z.atk > 0 ? Math.sin(z.atk / .45 * Math.PI) : 0; const rising = z.rise < 1 ? 1 : 0;
    for (let i = 0; i < 2; i++) { v.arms[i].rotation.x = v.armDown === i ? -.2 + Math.sin(ph) * .3 : -1.35 + Math.sin(t * 2 + i * 2) * .12 - atk * .7 - rising * 1.2; v.arms[i].rotation.z = (i ? -1 : 1) * (.12 + atk * .2); v.fore[i].rotation.x = -.25 - atk * .5; }
    v.torso.rotation.x = .26 + Math.sin(ph * 2) * .05 + atk * .25; v.torso.rotation.z = Math.sin(ph) * .07 + (v.limp ? .12 : 0);
    v.head.rotation.z = Math.sin(t * 2.7) * .18; v.head.rotation.x = -.15 + Math.sin(t * 1.3) * .1;
    if (z.atk > 0 && !v.lastAtk) sGroan(distVol(z.x, z.z, 14)); v.lastAtk = z.atk > 0 ? 1 : 0;
    if (Math.random() < dt * .16) sGroan(distVol(z.x, z.z, 26) * .7);
  }
  for (let i = corpses.length - 1; i >= 0; i--) { const c = corpses[i]; c.t += dt; const f = Math.min(1, c.t / .5);
    c.v.body.rotation.x = -f * f * Math.PI / 2; c.v.body.position.y = f * .16; c.v.arms[0].rotation.x = c.v.arms[1].rotation.x = -1.35 + f * 1.2;
    if (c.t > 6) c.v.g.position.y -= dt * .25; if (c.t > 8) { zGroup.remove(c.v.g); corpses.splice(i, 1); } }
  for (const id in players) { const p = players[id]; if (id === G.myId) continue; if (!p.view) makePlayerView(p); const v = p.view, g = v.g, ox = g.position.x, oz = g.position.z;
    g.position.x += (p.x - ox) * k; g.position.z += (p.z - oz) * k; g.position.y = p.y; g.rotation.y = lerpAngle(g.rotation.y, p.yaw + Math.PI, dt * 12);
    v.ph += Math.hypot(g.position.x - ox, g.position.z - oz) * 3; v.legs[0].rotation.x = Math.sin(v.ph) * .6; v.legs[1].rotation.x = -Math.sin(v.ph) * .6;
    v.torso.rotation.x = -p.pitch * .5; v.body.rotation.x = p.down ? -Math.PI / 2 : 0; v.body.position.y = p.down ? .2 : 0;
    if (v.seq !== p.fireSeq) { v.seq = p.fireSeq; sShot(p.wid, distVol(p.x, p.z, 45) * .8); remoteFlash.position.set(p.x - Math.sin(p.yaw) * .8, 1.4, p.z - Math.cos(p.yaw) * .8); remoteFlash.intensity = 2.5; setTimeout(() => { remoteFlash.intensity = 0; }, 50); } }
  // power-up drops
  const seen = {};
  for (const d of drops) { seen[d.id] = 1; let m = dropMeshes[d.id];
    if (!m) { const col = { ammo: 0x40ff60, insta: 0xff4030, nuke: 0xffd040 }[d.type]; m = new THREE.Mesh(new THREE.OctahedronGeometry(.28), new THREE.MeshBasicMaterial({ color: col }));
      const l = new THREE.PointLight(col, .9, 6, 1.6); m.add(l); scene.add(m); dropMeshes[d.id] = m; }
    m.position.set(d.x, 1 + Math.sin(G.time * 3) * .12, d.z); m.rotation.y = G.time * 2; }
  for (const id in dropMeshes) if (!seen[id]) { scene.remove(dropMeshes[id]); delete dropMeshes[id]; }
}

// ---------------------------------------------------------------- HUD
let lastRound = -1, hudCache = {};
function setH(id, html) { if (hudCache[id] !== html) { hudCache[id] = html; $(id).innerHTML = html; } }
function showMsg(t, dur) { $('msg').textContent = t; msgT = dur || 2.5; }
function esc(s) { return String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c])); }
function updateHUD(dt) {
  const w = curW(), d = WEAPONS[w.id];
  setH('wname', d.name); setH('am', String(w.ammo)); setH('rs', ' / ' + w.reserve);
  $('am').style.color = w.ammo <= d.mag * .25 ? '#e04040' : '#f0f0e8';
  setH('round', G.round > 0 ? String(G.round) : '');
  const left = G.host ? G.toSpawn + zombies.length : (G.left || 0);
  setH('left', G.state === 'wave' ? left + ' remaining' : G.round > 0 ? 'Next wave incoming' : 'They are coming');
  setH('scores', Object.values(players).sort((a, b) => b.points - a.points).map(p => `<div class="${p.id === G.myId ? 'me' : ''} ${p.down ? 'down' : ''}">${esc(p.name)}${p.down ? ' (down)' : ''} &nbsp; ${p.points}</div>`).join(''));
  $('hpbar').style.width = Math.max(0, me.hp / me.maxHp * 100) + '%'; $('hpbar').style.background = me.hp < me.maxHp * .4 ? '#c03030' : '#b8c4a0';
  $('hurt').style.opacity = Math.min(1, L.hurt * .8 + (me.down ? .8 : Math.max(0, 1 - me.hp / me.maxHp) * .7));
  $('hit').style.opacity = L.hitFx; $('cross').style.opacity = L.ads > .5 || me.down ? 0 : 1;
  const it = nearestInteractable(); setH('prompt', me.down ? 'You are down. You get back up if your team survives the wave.' : it ? promptFor(it) : '');
  setH('power', G.insta > 0 ? 'OVERKILL ' + Math.ceil(G.insta) : '');
  if (G.round !== lastRound) { if (G.round > 0) { showMsg('WAVE ' + G.round, 3.5); sTone(98, 2.2, .3, 'sawtooth', 0, 49); sTone(147, 2.2, .2, 'sawtooth', .1, 73); } lastRound = G.round; }
  if (msgT > 0) { msgT -= dt; $('msg').style.opacity = Math.min(1, msgT * 2); } else $('msg').style.opacity = 0;
  $('lockhint').style.display = document.pointerLockElement || G.over ? 'none' : 'block';
}
function gameOver() {
  document.exitPointerLock && document.exitPointerLock();
  $('overtext').textContent = `You survived ${Math.max(0, G.round - 1)} wave${G.round - 1 === 1 ? '' : 's'} — ${me.kills} kills`;
  $('over').style.display = 'flex';
}

// ---------------------------------------------------------------- networking setup
const status = t => { $('status').textContent = t; };
function lockMouse() { try { const r = renderer.domElement.requestPointerLock(); if (r && r.catch) r.catch(() => {}); } catch (e) {} }
function beginGame(isHost, id) {
  initAudio(); G.host = isHost; G.myId = id; G.started = true;
  me = players[id] = newPlayer(id, ($('name').value || 'Survivor').slice(0, 14)); me.x = SPAWN.x + (isHost ? 0 : rnd(-1.5, 1.5)); me.z = SPAWN.z + (isHost ? 0 : rnd(-1.5, 1.5)); me.yaw = Math.PI; L.lastHp = me.hp;
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
    c.on('open', () => { status('Joining…'); c.send({ t: 'hello', name: ($('name').value || 'Survivor').slice(0, 14) });
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
  renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5)); renderer.setSize(innerWidth, innerHeight);
  renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 1.15; renderer.outputEncoding = THREE.sRGBEncoding; renderer.autoClear = false;
  scene = new THREE.Scene(); scene.background = new THREE.Color(0x04060a); scene.fog = new THREE.FogExp2(0x04060a, .055);
  camera = new THREE.PerspectiveCamera(72, innerWidth / innerHeight, .05, 200); camera.rotation.order = 'YXZ'; scene.add(camera);
  clock = new THREE.Clock(); raycaster = new THREE.Raycaster();
  flashlight = new THREE.SpotLight(0xfff1d6, 2.3, 34, .5, .55, 1.4); flashlight.position.set(.22, -.18, 0); flashlight.castShadow = true;
  flashlight.shadow.mapSize.set(1024, 1024); flashlight.shadow.camera.near = .3; flashlight.shadow.camera.far = 34; flashlight.shadow.bias = -.002;
  camera.add(flashlight); flashlight.target.position.set(0, 0, -6); camera.add(flashlight.target);
  muzzleLight = new THREE.PointLight(0xffc070, 0, 16, 1.5); muzzleLight.position.set(0, 0, -1); camera.add(muzzleLight);
  remoteFlash = new THREE.PointLight(0xffc070, 0, 14, 1.5); scene.add(remoteFlash);
  zGroup = new THREE.Group(); scene.add(zGroup);
  initGeo(); initLevelMats(); buildWeaponScene(); buildFX(); loadMap('ward');
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
  });
  addEventListener('keyup', e => { keys[e.code] = false; });
  addEventListener('blur', () => { for (const k in keys) keys[k] = false; mouse.l = mouse.r = false; });
  const cv = renderer.domElement;
  cv.addEventListener('mousedown', e => { if (!G.started || G.over) return; if (!document.pointerLockElement) { lockMouse(); return; } if (e.button === 0) mouse.l = true; if (e.button === 2) mouse.r = true; if (e.button === 1) { e.preventDefault(); melee(); } });
  addEventListener('mouseup', e => { if (e.button === 0) mouse.l = false; if (e.button === 2) mouse.r = false; });
  addEventListener('contextmenu', e => e.preventDefault());
  addEventListener('wheel', () => { if (G.started && L.weapons.length > 1) switchWeapon(1 - L.wi); });
  addEventListener('mousemove', e => { if (!me || me.down || document.pointerLockElement !== cv) return; const s = .0022 / (1 + (WEAPONS[curW().id].zoom - 1) * L.ads);
    me.yaw -= e.movementX * s; me.pitch = Math.max(-1.5, Math.min(1.5, me.pitch - e.movementY * s)); });
  $('solo').onclick = () => beginGame(true, 'h'); $('host').onclick = hostOnline; $('join').onclick = joinOnline;
  for (const id in MAPS) { const b = document.createElement('button'); b.className = 'mapbtn' + (id === MAPID ? ' sel' : ''); b.innerHTML = '<b>' + MAPS[id].name + '</b><span>' + MAPS[id].desc + '</span>';
    b.onclick = () => { if (G.started || id === MAPID) return; loadMap(id); document.querySelectorAll('.mapbtn').forEach(x => x.classList.remove('sel')); b.classList.add('sel'); }; $('maps').appendChild(b); }
  const jq = new URLSearchParams(location.search).get('join'); if (jq) { $('joincode').value = jq.toUpperCase().slice(0, 5); status('Invite code filled in — press Join game.'); }
  window.HW = { G, players, zombies, L, Net, MAPS, loadMap, hostHit, spawnZombie, drops, fire, melee, dealHit, camera: () => camera, map: () => ({ MAP, W, H, id: MAPID, spawn: SPAWN, zSpawns, colliders, lightSpots, interactables, navBlock, flow }) };
  frame();
}
let lastFrame = 0, lastTick = 0;
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
  renderer.clear(); renderer.render(scene, camera);
  if (G.started && me && !me.down) { renderer.clearDepth(); renderer.render(wscene, wcam); }
}
init();
})();
