'use strict';
(function () {
const $ = id => document.getElementById(id);
const TILE = 3, WALL_H = 3.6, EYE = 1.66, MAX_ALIVE = 24;

// ---------------------------------------------------------------- map
const MAP = [
  '############################',
  '#S...o#S...........#,,,,,,s#',
  '#.....#.....L......#,t,,,,,#',
  '#..L..a............b,,,,,,,#',
  '#.....#....##......#,,,M,,,#',
  '#.....#....##......#,,,,,,,#',
  '#o....#......P....o#,,,,,t,#',
  '#..A..#............#,,,,,,,#',
  '#.....#.....L.....S#s,,,,,,#',
  '###.#######c########,,t,,,,#',
  '#.....#o...........#,,,,,,,#',
  '#..L..#..S...L.....####d####',
  '#.....#....##......#.......#',
  '#.....e....##......f...L...#',
  '#.....#............#o......#',
  '#..S..#......L.....#..H....#',
  '#.....#............#.......#',
  '#....o#..S........o#.....S.#',
  '#..L..#............#...L...#',
  '#.....#............#.......#',
  '############################'
];
const W = 28, H = MAP.length;
MAP.forEach((r, i) => { if (r.length !== W) console.error('map row', i, 'length', r.length); });
const DOORS = {
  a: { cost: 750, name: 'the West Ward' }, b: { cost: 1250, name: 'the Courtyard' },
  c: { cost: 1000, name: 'the South Hall' }, d: { cost: 1250, name: 'the Morgue' },
  e: { cost: 1000, name: 'the Service Corridor' }, f: { cost: 1000, name: 'the Morgue Passage' }
};
const COST = { crate: 950, ammo: 500, stim: 2500 };
const doorOpen = {}, doorMesh = {};
const tileAt = (c, r) => (c < 0 || r < 0 || c >= W || r >= H) ? '#' : MAP[r][c];
function solid(c, r) {
  const ch = tileAt(c, r);
  if (ch === '#') return true;
  if (DOORS[ch] && !doorOpen[ch]) return true;
  return false;
}
const isOutdoor = ch => ch === ',' || ch === 's' || ch === 't' || ch === 'M';
const wx = c => c * TILE + TILE / 2;
let SPAWN = { x: 0, z: 0 };
const zSpawns = [], interactables = [], colliders = [], lights = [];

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
  meleeT: 0, flash: true, crateT: 0, crateW: null, lastHp: 100, hurt: 0, wasDown: false, hitFx: 0, sprint: false, stepPh: 0 };
const keys = {}, mouse = { l: false, r: false };
const Net = { peer: null, conns: {}, conn: null, sendT: 0 };
let flashlight, muzzleLight, remoteFlash, zGroup, propGroup, doorGroup, shootables = [];
let crateObj = null, msgT = 0, flow = new Int16Array(W * H), flowT = 0;
const gunViews = {}; let gunRoot, muzzleFlash, wLight;
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

// ---------------------------------------------------------------- level
const MAT = {};
function buildLevel() {
  const bump = bumpTex();
  const std = (map, o) => new THREE.MeshStandardMaterial(Object.assign({ map, bumpMap: bump, bumpScale: .035, roughness: .92, metalness: 0 }, o || {}));
  MAT.wallA = std(wallTex(0)); MAT.wallB = std(wallTex(1));
  MAT.floor = std(canvasTex(512, (g, s) => {
    const n = 4, t = s / n;
    for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) { g.fillStyle = (i + j) % 2 ? '#5a5c53' : '#484a44'; g.fillRect(i * t, j * t, t, t); }
    g.strokeStyle = '#191a17'; g.lineWidth = 3; for (let i = 0; i <= n; i++) { g.beginPath(); g.moveTo(i * t, 0); g.lineTo(i * t, s); g.moveTo(0, i * t); g.lineTo(s, i * t); g.stroke(); }
    blotch(g, s, 30, '15,14,10', 20, 80, .45); blotch(g, s, 4, '85,8,6', 20, 60, .55); cracks(g, s, 5, 'rgba(10,10,8,.8)'); grainFx(g, s, 30);
  }), { roughness: .7 });
  MAT.ceil = std(canvasTex(512, (g, s) => {
    g.fillStyle = '#5b5b53'; g.fillRect(0, 0, s, s); g.strokeStyle = '#2a2a25'; g.lineWidth = 4;
    g.strokeRect(0, 0, s / 2, s / 2); g.strokeRect(s / 2, 0, s / 2, s / 2); g.strokeRect(0, s / 2, s / 2, s / 2); g.strokeRect(s / 2, s / 2, s / 2, s / 2);
    blotch(g, s, 12, '60,42,18', 30, 100, .5); blotch(g, s, 20, '20,20,18', 20, 60, .4); grainFx(g, s, 26);
  }));
  MAT.ground = std(canvasTex(512, (g, s) => {
    g.fillStyle = '#2b3023'; g.fillRect(0, 0, s, s); blotch(g, s, 70, '18,16,10', 15, 70, .6); blotch(g, s, 40, '60,70,40', 5, 25, .3);
    g.strokeStyle = 'rgba(70,84,44,.5)'; for (let i = 0; i < 500; i++) { const x = Math.random() * s, y = Math.random() * s; g.beginPath(); g.moveTo(x, y); g.lineTo(x + rnd(-3, 3), y - rnd(3, 9)); g.stroke(); }
    grainFx(g, s, 46);
  }), { roughness: 1 });
  MAT.door = std(canvasTex(256, (g, s) => {
    g.fillStyle = '#2a2018'; g.fillRect(0, 0, s, s);
    for (let i = 0; i < 6; i++) { g.fillStyle = `rgb(${rnd(60, 82) | 0},${rnd(42, 56) | 0},${rnd(26, 36) | 0})`; g.fillRect(i * s / 6 + 2, 0, s / 6 - 4, s); }
    g.save(); g.translate(s / 2, s / 2); for (const a of [-.35, .3, -.05]) { g.rotate(a); g.fillStyle = '#5a4630'; g.fillRect(-s, -16 + a * 90, s * 2, 30); g.fillStyle = '#18130e'; g.fillRect(-s, -16 + a * 90, s * 2, 2); } g.restore();
    blotch(g, s, 14, '10,8,5', 10, 40, .5); grainFx(g, s, 36);
  }), { roughness: .85 });
  MAT.rust = std(canvasTex(128, (g, s) => { g.fillStyle = '#4a3525'; g.fillRect(0, 0, s, s); blotch(g, s, 30, '110,55,20', 5, 25, .6); blotch(g, s, 20, '20,15,10', 5, 25, .6); grainFx(g, s, 40); }), { metalness: .5, roughness: .7 });
  MAT.wood = std(canvasTex(128, (g, s) => { g.fillStyle = '#3a2c1c'; g.fillRect(0, 0, s, s); for (let i = 0; i < 40; i++) { g.fillStyle = `rgba(${rnd(20, 90) | 0},${rnd(15, 60) | 0},20,.35)`; g.fillRect(0, Math.random() * s, s, rnd(1, 4)); } grainFx(g, s, 30); }));
  MAT.metal = new THREE.MeshStandardMaterial({ color: 0x23272a, metalness: .85, roughness: .42 });
  MAT.olive = new THREE.MeshStandardMaterial({ color: 0x39432a, metalness: .3, roughness: .7 });
  MAT.white = new THREE.MeshStandardMaterial({ color: 0x9a9c94, metalness: .2, roughness: .6 });
  MAT.bark = new THREE.MeshStandardMaterial({ color: 0x1c1712, roughness: 1 });

  const walls = [[], []], floors = [], ceils = [], grounds = [];
  for (let r = 0; r < H; r++) for (let c = 0; c < W; c++) {
    const ch = MAP[r][c], x = wx(c), z = wx(r);
    if (ch === '#') { walls[(c * 7 + r * 13) % 5 === 0 ? 1 : 0].push([x, z]); continue; }
    if (isOutdoor(ch)) grounds.push([x, z]); else { floors.push([x, z]); ceils.push([x, z]); }
    if (ch === 'P') SPAWN = { x, z };
    if (ch === 'S' || ch === 's') zSpawns.push({ c, r, x, z });
    if (ch === 'L') addCeilingLight(x, z);
    if (DOORS[ch]) addDoor(ch, c, r);
    if (ch === 'o') addBarrel(x, z);
    if (ch === 't') addTree(x, z);
    if (ch === 'M') addCrate(x, z);
    if (ch === 'A') addStation('ammo', x, z);
    if (ch === 'H') addStation('stim', x, z);
  }
  const inst = (geo, mat, list, y) => {
    const m = new THREE.InstancedMesh(geo, mat, list.length), o = new THREE.Object3D();
    list.forEach((p, i) => { o.position.set(p[0], y, p[1]); o.updateMatrix(); m.setMatrixAt(i, o.matrix); });
    m.frustumCulled = false; m.castShadow = true; m.receiveShadow = true; scene.add(m); shootables.push(m); return m;
  };
  const box = new THREE.BoxGeometry(TILE, WALL_H, TILE);
  inst(box, MAT.wallA, walls[0], WALL_H / 2); inst(box, MAT.wallB, walls[1], WALL_H / 2);
  const fg = new THREE.PlaneGeometry(TILE, TILE); fg.rotateX(-Math.PI / 2);
  const cg = new THREE.PlaneGeometry(TILE, TILE); cg.rotateX(Math.PI / 2);
  inst(fg, MAT.floor, floors, 0); inst(cg, MAT.ceil, ceils, WALL_H); inst(fg, MAT.ground, grounds, 0);

  // moon + courtyard glow
  const moon = new THREE.Mesh(new THREE.SphereGeometry(4, 16, 12), new THREE.MeshBasicMaterial({ color: 0xbfc8d8, fog: false }));
  moon.position.set(wx(30), 60, wx(-8)); scene.add(moon);
  const cl = new THREE.PointLight(0x5b72a0, .55, 30, 1.6); cl.position.set(wx(23), 9, wx(5)); scene.add(cl);
}
function addCeilingLight(x, z) {
  const l = new THREE.PointLight(0xd9e2b0, .9, 11, 1.8); l.position.set(x, WALL_H - .35, z); scene.add(l);
  const fix = new THREE.Mesh(new THREE.BoxGeometry(1.1, .08, .28), new THREE.MeshBasicMaterial({ color: 0xe8efc0 })); fix.position.set(x, WALL_H - .05, z); scene.add(fix);
  lights.push({ l, fix, base: rnd(.6, 1), mode: Math.random() < .55 ? 1 : 0, ph: Math.random() * 99, v: 1 });
}
function addDoor(ch, c, r) {
  const m = new THREE.Mesh(new THREE.BoxGeometry(TILE, WALL_H, .4), MAT.door); m.position.set(wx(c), WALL_H / 2, wx(r));
  if (!(solid(c - 1, r) && solid(c + 1, r))) m.rotation.y = Math.PI / 2;
  m.castShadow = m.receiveShadow = true; doorGroup.add(m); doorMesh[ch] = m;
  interactables.push({ type: 'door', id: ch, x: wx(c), z: wx(r), cost: DOORS[ch].cost, range: 3 });
}
function openDoor(ch) {
  if (doorOpen[ch]) return; doorOpen[ch] = true;
  const m = doorMesh[ch]; if (m) { doorGroup.remove(m); if (G.started) { burst(m.position, 30, [.25, .18, .1], 3); sNoise(300, .5, distVol(m.position.x, m.position.z, 40)); } }
  flowT = 0;
}
function addBarrel(x, z) {
  const b = new THREE.Mesh(new THREE.CylinderGeometry(.38, .38, 1.1, 14), MAT.rust); b.position.set(x, .55, z); b.castShadow = b.receiveShadow = true; propGroup.add(b);
  const k = new THREE.Mesh(new THREE.BoxGeometry(.7, .6, .7), MAT.wood); k.position.set(x + .75, .3, z + .2); k.rotation.y = rnd(0, 1); k.castShadow = k.receiveShadow = true; propGroup.add(k);
  colliders.push({ x, z, r: .5 }, { x: x + .75, z: z + .2, r: .5 });
}
function addTree(x, z) {
  const t = new THREE.Mesh(new THREE.CylinderGeometry(.14, .3, 5.5, 8), MAT.bark); t.position.set(x, 2.75, z); t.castShadow = true; propGroup.add(t);
  for (let i = 0; i < 6; i++) { const b = new THREE.Mesh(new THREE.CylinderGeometry(.02, .07, rnd(1.4, 2.6), 5), MAT.bark);
    b.position.set(x, rnd(2.6, 5.2), z); b.rotation.set(rnd(-1.1, 1.1), rnd(0, 6), rnd(-1.1, 1.1)); b.translateY(.9); b.castShadow = true; propGroup.add(b); }
  colliders.push({ x, z, r: .4 });
}
function signMat(draw, col) {
  return new THREE.MeshBasicMaterial({ map: canvasTex(128, (g, s) => { g.fillStyle = '#060606'; g.fillRect(0, 0, s, s); g.fillStyle = col; g.strokeStyle = col; draw(g, s); }), });
}
function addCrate(x, z) {
  const g = new THREE.Group(); g.position.set(x, 0, z);
  const base = new THREE.Mesh(new THREE.BoxGeometry(1.6, .62, .85), MAT.wood); base.position.y = .31; g.add(base);
  for (const sx of [-.6, .6]) { const band = new THREE.Mesh(new THREE.BoxGeometry(.1, .66, .89), MAT.metal); band.position.set(sx, .32, 0); g.add(band); }
  const lidP = new THREE.Group(); lidP.position.set(0, .62, -.425); g.add(lidP);
  const lid = new THREE.Mesh(new THREE.BoxGeometry(1.6, .12, .85), MAT.wood); lid.position.set(0, .06, .425); lidP.add(lid);
  const sm = signMat((c, s) => { c.font = '900 100px Georgia'; c.textAlign = 'center'; c.fillText('?', s / 2, s * .78); }, '#58b8ff');
  for (const sz of [-1, 1]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.42, .42), sm); q.position.set(0, .31, sz * .431); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
  const glow = new THREE.PointLight(0x4aa8ff, .7, 7, 1.6); glow.position.y = 1.1; g.add(glow);
  g.traverse(o => { if (o.isMesh) { o.castShadow = true; o.receiveShadow = true; } });
  propGroup.add(g); colliders.push({ x: x - .4, z, r: .55 }, { x: x + .4, z, r: .55 });
  const show = new THREE.Group(); show.position.set(x, 1.1, z); scene.add(show);
  crateObj = { g, lidP, glow, show, models: {} };
  for (const id in WEAPONS) { if (id === 'pistol') continue; const m = buildGun(id, false); m.scale.setScalar(1.6); m.rotation.y = Math.PI / 2; m.visible = false; show.add(m); crateObj.models[id] = m; }
  interactables.push({ type: 'crate', x, z, cost: COST.crate, range: 2.4 });
}
function addStation(type, x, z) {
  const g = new THREE.Group(); g.position.set(x, 0, z);
  if (type === 'ammo') {
    const b = new THREE.Mesh(new THREE.BoxGeometry(1.2, .8, .75), MAT.olive); b.position.y = .4; g.add(b);
    const sm = signMat((c, s) => { for (let i = 0; i < 4; i++) { c.fillRect(22 + i * 24, 44, 14, 60); c.beginPath(); c.arc(29 + i * 24, 44, 7, Math.PI, 0); c.fill(); } }, '#ffd040');
    for (const sz of [-1, 1]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.5, .5), sm); q.position.set(0, .42, sz * .381); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
    const l = new THREE.PointLight(0xffc040, .35, 5, 1.6); l.position.y = 1.2; g.add(l);
    interactables.push({ type: 'ammo', x, z, cost: COST.ammo, range: 2.3 }); colliders.push({ x, z, r: .7 });
  } else {
    const b = new THREE.Mesh(new THREE.BoxGeometry(.95, 1.9, .6), MAT.white); b.position.y = .95; g.add(b);
    const sm = signMat((c, s) => { c.fillRect(s * .38, s * .12, s * .24, s * .76); c.fillRect(s * .12, s * .38, s * .76, s * .24); }, '#ff3030');
    for (const sz of [-1, 1]) { const q = new THREE.Mesh(new THREE.PlaneGeometry(.55, .55), sm); q.position.set(0, 1.3, sz * .306); if (sz < 0) q.rotation.y = Math.PI; g.add(q); }
    const l = new THREE.PointLight(0xff3838, .4, 5, 1.6); l.position.set(0, 1.4, .8); g.add(l);
    interactables.push({ type: 'stim', x, z, cost: COST.stim, range: 2.3 }); colliders.push({ x, z, r: .65 });
  }
  g.traverse(o => { if (o.isMesh) { o.castShadow = true; o.receiveShadow = true; } });
  propGroup.add(g);
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
const V3 = (x, y, z) => new THREE.Vector3(x, y, z);
function M(x, y, z, rx, ry, rz, sx, sy, sz) {
  return new THREE.Matrix4().compose(V3(x, y, z), new THREE.Quaternion().setFromEuler(new THREE.Euler(rx || 0, ry || 0, rz || 0)), V3(sx || 1, sy || 1, sz || 1));
}
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
  MAT.gear = new THREE.MeshStandardMaterial({ color: 0x2c3327, roughness: .9 }); MAT.gear2 = new THREE.MeshStandardMaterial({ color: 0x1a1c1e, roughness: .8 });
  MAT.pskin = new THREE.MeshStandardMaterial({ color: 0x9a7a66, roughness: .8 });
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
  if (o.player) mk(GEO.helmet, MAT.gear2, head, 0, .15, 0);
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
  const v = buildHumanoid({ skin: MAT.pskin, face: MAT.pskin, cloth: MAT.gear, pants: MAT.gear2, shoe: MAT.dark, player: true });
  const gun = buildGun(p.wid === 'pistol' ? 'rifle' : p.wid, false); gun.rotation.y = Math.PI; gun.position.set(.08, .5, .4); v.torso.add(gun);
  v.arms[0].rotation.x = -1.25; v.arms[0].rotation.z = -.35; v.arms[1].rotation.x = -1.1; v.arms[1].rotation.z = .25;
  const c = document.createElement('canvas'); c.width = 256; c.height = 64; const g = c.getContext('2d');
  g.font = '700 30px Arial'; g.textAlign = 'center'; g.fillStyle = '#d8e6c0'; g.shadowColor = '#000'; g.shadowBlur = 6; g.fillText(p.name || 'Player', 128, 42);
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
  for (const li of lights) {
    if (li.mode) { if (Math.random() < dt * 6) li.v = Math.random() < .3 ? rnd(0, .25) : rnd(.7, 1); } else li.v = .9 + Math.sin(G.time * 9 + li.ph) * .05;
    li.l.intensity = li.base * li.v; li.fix.material.color.setScalar(.15 + li.v * .8);
  }
}
function bloodDecal(x, z) { const m = bloods[bloodI = (bloodI + 1) % bloods.length]; m.position.set(x, .015 + bloodI * .0004, z); m.rotation.y = rnd(0, 6); const s = rnd(.6, 1.3); m.scale.set(s, 1, s); m.visible = true; }

// ---------------------------------------------------------------- players
function newPlayer(id, name) {
  return { id, name: name || 'Survivor', x: SPAWN.x + rnd(-1.5, 1.5), y: 0, z: SPAWN.z + rnd(-1.5, 1.5), yaw: 0, pitch: 0, hp: 100, maxHp: 100, down: false,
    points: 500, kills: 0, wid: 'pistol', fireSeq: 0, lastHurt: -99, view: null };
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
function melee() {
  if (L.meleeT > 0 || me.down) return; L.meleeT = .65; sNoise(900, .12, .3, 'bandpass');
  camera.getWorldDirection(_d); const h = castShot(_d, 2.3);
  if (h && h.object.userData.zr) { burst(h.point, 12, [.4, .02, .02], 2); dealHit(h.object.userData.zr.id, 150, false); L.hitFx = 1; sNoise(200, .12, .6); }
}
function dealHit(zid, dmg, head) { if (G.host) hostHit(G.myId, zid, dmg, head); else netSend({ t: 'hit', z: zid, d: Math.round(dmg), h: head ? 1 : 0 }); }

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

// ---------------------------------------------------------------- host simulation
function buildFlow() {
  flow.fill(9999); const q = [];
  for (const id in players) { const p = players[id]; if (p.down) continue; const c = Math.floor(p.x / TILE), r = Math.floor(p.z / TILE); if (solid(c, r)) continue; const i = r * W + c; if (flow[i] !== 0) { flow[i] = 0; q.push(i); } }
  for (let h = 0; h < q.length; h++) { const i = q[h], c = i % W, r = (i / W) | 0, d = flow[i] + 1;
    for (const [dc, dr] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) { const nc = c + dc, nr = r + dr; if (solid(nc, nr)) continue; const ni = nr * W + nc; if (flow[ni] > d) { flow[ni] = d; q.push(ni); } } }
}
const N8 = [[1, 0], [-1, 0], [0, 1], [0, -1], [1, 1], [1, -1], [-1, 1], [-1, -1]];
function spawnZombie() {
  const ok = zSpawns.filter(s => flow[s.r * W + s.c] < 9000); if (!ok.length) return false;
  const far = ok.filter(s => flow[s.r * W + s.c] >= 3); const s = (far.length ? far : ok)[(Math.random() * (far.length ? far.length : ok.length)) | 0];
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
function hostHit(pid, zid, dmg, head) {
  const z = zById[zid], p = players[pid]; if (!z || !p) return;
  z.hp -= G.insta > 0 ? 1e9 : dmg; p.points += 10;
  if (z.hp <= 0) {
    p.points += head ? 90 : 50; p.kills++;
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
    if (G.toSpawn > 0 && G.spawnT <= 0 && zombies.length < MAX_ALIVE) { if (spawnZombie()) G.toSpawn--; G.spawnT = Math.max(.35, 2 - G.round * .12); }
    if (G.toSpawn <= 0 && !zombies.length) { G.state = 'inter'; G.interT = 9; }
  }
  for (const z of zombies) {
    if (z.rise < 1) { z.rise = Math.min(1, z.rise + dt / 1.5); continue; }
    let tp = null, td = 1e9; for (const p of alive) { const d = Math.hypot(p.x - z.x, p.z - z.z); if (d < td) { td = d; tp = p; } }
    if (!tp) continue;
    let gx = tp.x, gz = tp.z; const c = Math.floor(z.x / TILE), r = Math.floor(z.z / TILE), here = flow[r * W + c];
    if (here > 1 && here < 9000) { let best = here, bc = c, br = r;
      for (const [dc, dr] of N8) { const nc = c + dc, nr = r + dr; if (solid(nc, nr)) continue; if (dc && dr && (solid(c + dc, r) || solid(c, r + dr))) continue;
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
  Net.sendT -= dt; if (Net.sendT <= 0) { Net.sendT = 1 / 12; sendSnapshot(); }
}
const r2 = v => Math.round(v * 100) / 100;
function sendSnapshot() {
  if (!Object.keys(Net.conns).length) return;
  broadcast({ t: 's', r: G.round, st: G.state, it: r2(G.interT), left: G.toSpawn + zombies.length, insta: r2(Math.max(0, G.insta)), doors: Object.keys(doorOpen).join(''),
    P: Object.values(players).map(p => [p.id, p.name, r2(p.x), r2(p.y), r2(p.z), r2(p.yaw), r2(p.pitch), Math.round(p.hp), p.maxHp, p.down ? 1 : 0, p.points, p.kills, p.wid, p.fireSeq]),
    Z: zombies.map(z => [z.id, r2(z.x), r2(z.z), r2(z.rot), r2(z.rise), z.atk > 0 ? 1 : 0]), D: drops.map(d => [d.id, d.type, r2(d.x), r2(d.z)]) });
}
function hostRecv(pid, m) {
  if (!m || !m.t) return;
  if (m.t === 'hello') { if (!players[pid]) players[pid] = newPlayer(pid, String(m.name || 'Survivor').slice(0, 14)); }
  const p = players[pid]; if (!p) return;
  if (m.t === 'p') { p.x = +m.a[0] || 0; p.y = +m.a[1] || 0; p.z = +m.a[2] || 0; p.yaw = +m.a[3] || 0; p.pitch = +m.a[4] || 0; if (WEAPONS[m.a[5]]) p.wid = m.a[5]; p.fireSeq = m.a[6] | 0; }
  else if (m.t === 'hit') hostHit(pid, m.z, Math.min(600, +m.d || 0), !!m.h);
  else if (m.t === 'buy') hostBuy(pid, m);
}

// ---------------------------------------------------------------- client
function clientRecv(m) {
  if (!m || !m.t) return;
  if (m.t === 'ok') return onBuyOk(m);
  if (m.t === 'ev') return onEvent(m.k);
  if (m.t !== 's') return;
  G.round = m.r; G.state = m.st; G.interT = m.it; G.left = m.left; G.insta = m.insta;
  for (const ch of m.doors) if (!doorOpen[ch]) openDoor(ch);
  const seenP = {};
  for (const a of m.P) { const id = a[0]; seenP[id] = 1; let p = players[id]; if (!p) { p = players[id] = newPlayer(id, a[1]); }
    p.name = a[1]; p.hp = a[7]; p.maxHp = a[8]; p.down = !!a[9]; p.points = a[10]; p.kills = a[11];
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
function clientUpdate(dt) {
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
  const w = curW(), d = WEAPONS[w.id]; L.fireT -= dt; if (L.switchT > 0) L.switchT -= dt; if (L.meleeT > 0) L.meleeT -= dt;
  if (L.reloadT > 0) { L.reloadT -= dt; if (L.reloadT <= 0) { const n = Math.min(d.mag - w.ammo, w.reserve); w.ammo += n; w.reserve -= n; } }
  if (mouse.l && document.pointerLockElement && L.fireT <= 0 && L.reloadT <= 0 && L.switchT <= 0 && L.meleeT <= 0 && (d.auto || !L.fired)) {
    if (w.ammo > 0) fire(); else { L.fired = true; sTone(900, .03, .15, 'square'); startReload(); } }
  if (!mouse.l) L.fired = false;
  const wantAds = mouse.r && L.reloadT <= 0 && !L.sprint ? 1 : 0; L.ads += (wantAds - L.ads) * Math.min(1, dt * 14);
  L.kick = Math.max(0, L.kick - dt * 9); L.hitFx = Math.max(0, L.hitFx - dt * 5); L.hurt = Math.max(0, L.hurt - dt * 1.2);
  // crate animation
  if (L.crateT > 0) { L.crateT -= dt; const c = crateObj, k = 3.4 - L.crateT; c.lidP.rotation.x = -Math.min(1, k * 3) * 1.3; c.glow.intensity = 1.6;
    const ids = Object.keys(c.models), showId = L.crateT < .9 ? L.crateW : ids[Math.floor(k * 8) % ids.length];
    for (const id of ids) c.models[id].visible = id === showId; c.show.position.y = 1 + Math.min(.5, k * .4); c.show.rotation.y += dt * 1.5;
    if (L.crateT <= 0) { for (const id of ids) c.models[id].visible = false; c.lidP.rotation.x = 0; c.glow.intensity = .7; giveWeapon(L.crateW); showMsg(WEAPONS[L.crateW].name.toUpperCase(), 2); sNoise(2200, .08, .3); } }
  // camera
  const bobY = moving ? Math.sin(L.bob * 2) * (L.sprint ? .055 : .03) * (1 - L.ads * .7) : 0;
  camera.position.set(me.x, EYE + me.y + bobY, me.z); camera.rotation.set(me.pitch, me.yaw, moving ? Math.sin(L.bob) * .006 : 0);
  const fov = 72 / (1 + (d.zoom - 1) * L.ads) + (L.sprint ? 4 : 0); if (Math.abs(camera.fov - fov) > .05) { camera.fov += (fov - camera.fov) * Math.min(1, dt * 12); camera.updateProjectionMatrix(); }
  // view model
  for (const id in gunViews) gunViews[id].visible = id === w.id;
  const gv = gunViews[w.id], a = L.ads, rl = L.reloadT > 0 ? Math.sin((1 - L.reloadT / d.reload) * Math.PI) : 0, sw = Math.max(0, L.switchT) / .4, ml = L.meleeT > 0 ? Math.sin((1 - L.meleeT / .65) * Math.PI) : 0;
  const sprintK = L.sprint && moving ? 1 : 0;
  gunRoot.position.set(.165 * (1 - a) + Math.cos(L.bob) * .008 * (1 - a) * (moving ? 1 : 0) - sprintK * .05,
    -.135 * (1 - a) + gv.userData.adsY * a + (moving ? Math.abs(Math.sin(L.bob)) * .01 * (1 - a) : 0) - rl * .16 - sw * .3 - sprintK * .06 + Math.sin(G.time * 1.6) * .002,
    -.5 + (gv.userData.adsZ + .08) * a + L.kick * .05 - ml * .25);
  gunRoot.rotation.set(L.kick * .09 - rl * .8 + sprintK * -.25, sprintK * .6 + ml * .5, rl * .3 + ml * -.6);
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
  me = players[id] = newPlayer(id, ($('name').value || 'Survivor').slice(0, 14)); me.x = SPAWN.x; me.z = SPAWN.z; me.yaw = Math.PI;
  L.weapons = []; giveWeapon('pistol'); L.switchT = 0;
  $('menu').style.display = 'none'; $('hud').style.display = 'block'; camera.fov = 72; camera.updateProjectionMatrix();
  lockMouse();
}
function hostOnline() {
  if (typeof Peer === 'undefined') return status('Online play needs an internet connection (could not load the network library).');
  status('Creating room…'); const code = Array.from({ length: 5 }, () => 'ABCDEFGHJKLMNPQRSTUVWXYZ'[(Math.random() * 24) | 0]).join('');
  const peer = Net.peer = new Peer('hollowward-' + code);
  peer.on('open', () => { G.code = code; beginGame(true, 'h'); $('code').innerHTML = 'ROOM CODE: <b style="color:#dfd;font-size:17px;letter-spacing:4px">' + code + '</b> — friends enter this to join'; });
  peer.on('connection', c => {
    c.on('open', () => { if (Object.keys(players).length >= 4) { c.close(); return; } Net.conns[c.peer] = c; });
    c.on('data', m => hostRecv(c.peer, m));
    c.on('close', () => { delete Net.conns[c.peer]; removePlayer(c.peer); });
  });
  peer.on('error', e => { if (!G.started) status('Could not create room: ' + (e.type || e)); });
}
function joinOnline() {
  if (typeof Peer === 'undefined') return status('Online play needs an internet connection (could not load the network library).');
  const code = $('joincode').value.trim().toUpperCase(); if (code.length !== 5) return status('Enter the 5-letter room code from the host.');
  status('Connecting…'); const peer = Net.peer = new Peer();
  peer.on('open', id => { const c = Net.conn = peer.connect('hollowward-' + code, { reliable: true });
    c.on('open', () => { beginGame(false, id); c.send({ t: 'hello', name: me.name }); $('code').textContent = 'ROOM ' + code; });
    c.on('data', clientRecv);
    c.on('close', () => { if (!G.over) { showMsg('HOST DISCONNECTED', 99); } }); });
  peer.on('error', e => { if (!G.started) status(e.type === 'peer-unavailable' ? 'No game found with that code.' : 'Connection failed: ' + (e.type || e)); });
}

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
  scene.add(new THREE.HemisphereLight(0x31405c, 0x0a0a08, .22));
  flashlight = new THREE.SpotLight(0xfff1d6, 2.3, 34, .5, .55, 1.4); flashlight.position.set(.22, -.18, 0); flashlight.castShadow = true;
  flashlight.shadow.mapSize.set(1024, 1024); flashlight.shadow.camera.near = .3; flashlight.shadow.camera.far = 34; flashlight.shadow.bias = -.002;
  camera.add(flashlight); flashlight.target.position.set(0, 0, -6); camera.add(flashlight.target);
  muzzleLight = new THREE.PointLight(0xffc070, 0, 16, 1.5); muzzleLight.position.set(0, 0, -1); camera.add(muzzleLight);
  remoteFlash = new THREE.PointLight(0xffc070, 0, 14, 1.5); scene.add(remoteFlash);
  zGroup = new THREE.Group(); propGroup = new THREE.Group(); doorGroup = new THREE.Group(); scene.add(zGroup, propGroup, doorGroup);
  initGeo(); buildLevel(); buildWeaponScene(); buildFX();
  shootables.push(doorGroup, propGroup, zGroup);
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
    if (e.code === 'KeyF') { L.flash = !L.flash; sTone(1800, .03, .1, 'square'); } if (e.code === 'KeyV') melee();
    if (e.code === 'KeyE') { const it = nearestInteractable(); if (it) requestBuy(it); }
  });
  addEventListener('keyup', e => { keys[e.code] = false; });
  addEventListener('blur', () => { for (const k in keys) keys[k] = false; mouse.l = mouse.r = false; });
  const cv = renderer.domElement;
  cv.addEventListener('mousedown', e => { if (!G.started || G.over) return; if (!document.pointerLockElement) { lockMouse(); return; } if (e.button === 0) mouse.l = true; if (e.button === 2) mouse.r = true; });
  addEventListener('mouseup', e => { if (e.button === 0) mouse.l = false; if (e.button === 2) mouse.r = false; });
  addEventListener('contextmenu', e => e.preventDefault());
  addEventListener('wheel', () => { if (G.started && L.weapons.length > 1) switchWeapon(1 - L.wi); });
  addEventListener('mousemove', e => { if (!me || me.down || document.pointerLockElement !== cv) return; const s = .0022 / (1 + (WEAPONS[curW().id].zoom - 1) * L.ads);
    me.yaw -= e.movementX * s; me.pitch = Math.max(-1.5, Math.min(1.5, me.pitch - e.movementY * s)); });
  $('solo').onclick = () => beginGame(true, 'h'); $('host').onclick = hostOnline; $('join').onclick = joinOnline;
  window.HW = { G, players, zombies, L, hostHit, spawnZombie, drops, fire, dealHit, camera: () => camera };
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
  requestAnimationFrame(frame); lastFrame = performance.now(); const dt = Math.min(clock.getDelta(), .05); G.time += dt;
  if (!G.started) { const a = G.time * .12; camera.position.set(SPAWN.x + Math.cos(a) * 3, 1.7, SPAWN.z + Math.sin(a) * 3); camera.rotation.set(0, -a + Math.PI, 0); updateFX(dt); }
  else {
    updateLocal(dt);
    if (G.host) hostUpdate(dt); else clientUpdate(dt);
    updateViews(dt); updateFX(dt); updateHUD(dt);
  }
  renderer.clear(); renderer.render(scene, camera);
  if (G.started && me && !me.down) { renderer.clearDepth(); renderer.render(wscene, wcam); }
}
init();
})();
