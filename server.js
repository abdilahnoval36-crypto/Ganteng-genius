'use strict';
/*
 * Server Duel untuk Pokédex Stopwatch.
 * - Menyajikan file statis dari folder public/ (game-nya).
 * - Menjalankan WebSocket (implementasi RFC 6455 sendiri, tanpa library) untuk ruangan Duel.
 * Tidak ada dependency: cukup `node server.js`.
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');

const PORT = Number(process.env.PORT) || 3000;
const PUBLIC_DIR = path.join(__dirname, 'public');
// Kalau folder public/ tidak ada (file lepas satu folder), cukup sajikan index.html di sebelah server.js.
const FLAT = !fs.existsSync(PUBLIC_DIR);
const ROOT_DIR = FLAT ? __dirname : PUBLIC_DIR;

const N = 898;                 // jumlah Pokémon
const MAX_PLAYERS = 8;
const ROUND_TIMEOUT_MS = 120000; // ronde otomatis berakhir setelah 2 menit
const MAX_PAYLOAD = 16 * 1024;
const MAX_MS = 10 * 60 * 1000;
const SKEW_MS = 2500;          // toleransi selisih waktu klien vs server

/* ---------------------------------------------------------------- static */
const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8',
  '.png': 'image/png', '.svg': 'image/svg+xml', '.ico': 'image/x-icon', '.txt': 'text/plain; charset=utf-8'
};
const fileCache = new Map();

function loadFile(abs) {
  let hit = fileCache.get(abs);
  if (hit) return hit;
  const raw = fs.readFileSync(abs);
  const type = MIME[path.extname(abs).toLowerCase()] || 'application/octet-stream';
  const compressible = /^(text|application\/json|image\/svg)/.test(type);
  hit = { raw, gz: compressible ? zlib.gzipSync(raw, { level: 9 }) : null, type };
  fileCache.set(abs, hit);
  return hit;
}

const httpServer = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  if (url.pathname === '/healthz') {
    res.writeHead(200, { 'Content-Type': 'text/plain' });
    res.end('ok');
    return;
  }
  if (req.method !== 'GET' && req.method !== 'HEAD') {
    res.writeHead(405); res.end(); return;
  }
  let rel;
  try { rel = decodeURIComponent(url.pathname); } catch (e) { res.writeHead(400); res.end(); return; }
  if (rel === '/') rel = '/index.html';
  if (FLAT && rel !== '/index.html') { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('Tidak ditemukan'); return; }
  const abs = path.resolve(ROOT_DIR, '.' + rel);
  if (abs !== ROOT_DIR && !abs.startsWith(ROOT_DIR + path.sep)) { res.writeHead(403); res.end(); return; }
  let f;
  try {
    if (!fs.statSync(abs).isFile()) throw new Error('bukan file');
    f = loadFile(abs);
  } catch (e) { res.writeHead(404, { 'Content-Type': 'text/plain' }); res.end('Tidak ditemukan'); return; }
  const headers = { 'Content-Type': f.type, 'Cache-Control': 'no-cache', 'X-Content-Type-Options': 'nosniff' };
  const acceptsGzip = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
  let body = f.raw;
  if (f.gz && acceptsGzip) { body = f.gz; headers['Content-Encoding'] = 'gzip'; headers['Vary'] = 'Accept-Encoding'; }
  headers['Content-Length'] = body.length;
  res.writeHead(200, headers);
  res.end(req.method === 'HEAD' ? undefined : body);
});

/* ------------------------------------------------------------- websocket */
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const clients = new Set();

function parseFrame(buf) {
  if (buf.length < 2) return null;
  const b0 = buf[0], b1 = buf[1];
  const fin = (b0 & 0x80) !== 0, op = b0 & 0x0f, masked = (b1 & 0x80) !== 0;
  let len = b1 & 0x7f, off = 2;
  if (!masked) return { error: true };
  if (len === 126) { if (buf.length < 4) return null; len = buf.readUInt16BE(2); off = 4; }
  else if (len === 127) {
    if (buf.length < 10) return null;
    const big = buf.readBigUInt64BE(2);
    if (big > BigInt(MAX_PAYLOAD)) return { error: true };
    len = Number(big); off = 10;
  }
  if (len > MAX_PAYLOAD) return { error: true };
  if (buf.length < off + 4 + len) return null;
  const mask = buf.subarray(off, off + 4);
  const payload = Buffer.from(buf.subarray(off + 4, off + 4 + len));
  for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];
  return { fin, op, payload, used: off + 4 + len };
}

function makeFrame(op, payload) {
  const len = payload.length;
  let head;
  if (len < 126) head = Buffer.from([0x80 | op, len]);
  else if (len < 65536) { head = Buffer.alloc(4); head[0] = 0x80 | op; head[1] = 126; head.writeUInt16BE(len, 2); }
  else { head = Buffer.alloc(10); head[0] = 0x80 | op; head[1] = 127; head.writeBigUInt64BE(BigInt(len), 2); }
  return Buffer.concat([head, payload]);
}

class Client {
  constructor(socket) {
    this.socket = socket;
    this.buf = Buffer.alloc(0);
    this.frag = null;
    this.fragSize = 0;
    this.alive = true;
    this.closed = false;
    this.id = crypto.randomBytes(4).toString('hex');
    this.room = null;
    this.msgCount = 0;
    socket.setNoDelay(true);
    socket.on('data', (d) => this.onData(d));
    socket.on('close', () => this.onClose());
    socket.on('error', () => socket.destroy());
  }
  onData(d) {
    this.buf = Buffer.concat([this.buf, d]);
    if (this.buf.length > MAX_PAYLOAD * 2) { this.close(1009); return; }
    for (;;) {
      const f = parseFrame(this.buf);
      if (!f) break;
      if (f.error) { this.close(1002); return; }
      this.buf = this.buf.subarray(f.used);
      this.onFrame(f);
      if (this.closed) return;
    }
  }
  onFrame(f) {
    this.alive = true;
    if (f.op === 0x8) { this.close(1000); return; }
    if (f.op === 0x9) { this.raw(makeFrame(0xA, f.payload)); return; }
    if (f.op === 0xA) return;
    if (f.op === 0x1 || f.op === 0x0) {
      if (f.op === 0x1) { this.frag = []; this.fragSize = 0; }
      else if (!this.frag) return;
      this.frag.push(f.payload);
      this.fragSize += f.payload.length;
      if (this.fragSize > MAX_PAYLOAD) { this.close(1009); return; }
      if (f.fin) {
        const text = Buffer.concat(this.frag).toString('utf8');
        this.frag = null;
        this.onText(text);
      }
    }
  }
  onText(text) {
    this.msgCount++;
    if (this.msgCount > 200) { this.close(1008); return; } // batas pesan per jendela waktu
    let msg;
    try { msg = JSON.parse(text); } catch (e) { return; }
    if (!msg || typeof msg !== 'object' || typeof msg.t !== 'string') return;
    try { handle(this, msg); } catch (e) { console.error('handler error', e); }
  }
  raw(buf) { if (!this.closed && this.socket.writable) this.socket.write(buf); }
  send(obj) { this.raw(makeFrame(0x1, Buffer.from(JSON.stringify(obj)))); }
  close(code) {
    if (this.closed) return;
    const p = Buffer.alloc(2); p.writeUInt16BE(code || 1000, 0);
    try { this.socket.write(makeFrame(0x8, p)); } catch (e) { /* abaikan */ }
    this.socket.end();
    setTimeout(() => this.socket.destroy(), 1000).unref();
    this.onClose();
  }
  onClose() {
    if (this.closed) return;
    this.closed = true;
    clients.delete(this);
    leaveRoom(this);
  }
}

httpServer.on('upgrade', (req, socket) => {
  const key = req.headers['sec-websocket-key'];
  if (String(req.headers.upgrade || '').toLowerCase() !== 'websocket' || !key) { socket.destroy(); return; }
  const accept = crypto.createHash('sha1').update(key + WS_GUID).digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
  const c = new Client(socket);
  clients.add(c);
});

setInterval(() => {            // detak jantung: buang koneksi yang sudah mati
  for (const c of clients) {
    c.msgCount = 0;
    if (!c.alive) { c.socket.destroy(); c.onClose(); continue; }
    c.alive = false;
    c.raw(makeFrame(0x9, Buffer.alloc(0)));
  }
}, 30000).unref();

/* ------------------------------------------------------------------ game */
const rooms = new Map();
const CODE_CHARS = 'ABCDEFGHJKLMNPQRSTUVWXYZ';

function newCode() {
  for (let i = 0; i < 200; i++) {
    let code = '';
    for (let k = 0; k < 4; k++) code += CODE_CHARS[crypto.randomInt(CODE_CHARS.length)];
    if (!rooms.has(code)) return code;
  }
  return null;
}
function cleanName(n) {
  let s = typeof n === 'string' ? n.replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 16) : '';
  return s || 'Pemain';
}
function uniqueName(room, name) {
  const used = new Set([...room.players.values()].map((p) => p.name.toLowerCase()));
  if (!used.has(name.toLowerCase())) return name;
  for (let i = 2; i < 100; i++) {
    const cand = name.slice(0, 13) + ' ' + i;
    if (!used.has(cand.toLowerCase())) return cand;
  }
  return name;
}
function dexFromMs(ms) {
  const cs = Math.floor(ms / 10);
  return (((cs - 1) % N) + N) % N + 1;
}
function send(c, obj) { c.send(obj); }

function snapshotFor(room, client) {
  const showTarget = room.phase !== 'lobby';
  return {
    t: 'room',
    code: room.code,
    you: client.id,
    hostId: room.hostId,
    phase: room.phase,
    round: room.round,
    target: showTarget ? room.target : 0,
    deadline: room.phase === 'play' ? room.deadline : 0,
    players: [...room.players.values()].map((p) => ({
      id: p.id, name: p.name, score: p.score, status: p.status, host: p.id === room.hostId
    })),
    results: room.phase === 'result' ? room.results : null
  };
}
function broadcast(room) {
  for (const p of room.players.values()) send(p.client, snapshotFor(room, p.client));
}
function leaveRoom(client) {
  const room = client.room;
  if (!room) return;
  client.room = null;
  room.players.delete(client.id);
  if (room.players.size === 0) {
    clearTimeout(room.timer);
    rooms.delete(room.code);
    return;
  }
  if (room.hostId === client.id) room.hostId = room.players.keys().next().value;
  if (room.phase === 'play' && allDone(room)) { finishRound(room); return; }
  broadcast(room);
}
function allDone(room) {
  for (const p of room.players.values()) if (p.status !== 'done') return false;
  return room.players.size > 0;
}
function finishRound(room) {
  clearTimeout(room.timer);
  room.phase = 'result';
  const done = [...room.players.values()].filter((p) => p.status === 'done');
  done.sort((a, b) => a.diff - b.diff || a.ms - b.ms);
  const POINTS = [3, 2, 1];
  const rows = [];
  let rank = 0, lastDiff = null;
  done.forEach((p, i) => {
    if (p.diff !== lastDiff) { rank = i + 1; lastDiff = p.diff; }
    let gain = rank <= 3 ? POINTS[rank - 1] : 0;
    if (p.diff === 0) gain += 2;
    p.score += gain;
    rows.push({ id: p.id, name: p.name, ms: p.ms, n: p.n, diff: p.diff, rank, gain });
  });
  for (const p of room.players.values()) {
    if (p.status !== 'done') rows.push({ id: p.id, name: p.name, ms: null, n: 0, diff: null, rank: 0, gain: 0 });
  }
  room.results = rows;
  broadcast(room);
}
function startRound(room) {
  room.round++;
  room.target = 1 + crypto.randomInt(N);
  room.phase = 'play';
  room.results = null;
  room.deadline = Date.now() + ROUND_TIMEOUT_MS;
  for (const p of room.players.values()) { p.status = 'wait'; p.startedAt = 0; p.ms = 0; p.n = 0; p.diff = 0; }
  clearTimeout(room.timer);
  room.timer = setTimeout(() => { if (room.phase === 'play') finishRound(room); }, ROUND_TIMEOUT_MS);
  broadcast(room);
}
function addPlayer(room, client, name) {
  const p = { id: client.id, name: uniqueName(room, name), score: 0, status: 'wait', startedAt: 0, ms: 0, n: 0, diff: 0, client };
  room.players.set(client.id, p);
  client.room = room;
}

function handle(c, m) {
  switch (m.t) {
    case 'create': {
      leaveRoom(c);
      const code = newCode();
      if (!code) { send(c, { t: 'err', m: 'Server penuh, coba lagi nanti.' }); return; }
      const room = { code, hostId: c.id, players: new Map(), phase: 'lobby', round: 0, target: 0, results: null, timer: null, deadline: 0 };
      rooms.set(code, room);
      addPlayer(room, c, cleanName(m.name));
      broadcast(room);
      return;
    }
    case 'join': {
      const code = typeof m.code === 'string' ? m.code.trim().toUpperCase().slice(0, 4) : '';
      const room = rooms.get(code);
      if (!room) { send(c, { t: 'err', m: 'Ruangan ' + (code || '') + ' tidak ditemukan.' }); return; }
      if (c.room === room) return;
      if (room.players.size >= MAX_PLAYERS) { send(c, { t: 'err', m: 'Ruangan penuh (maksimal ' + MAX_PLAYERS + ' pemain).' }); return; }
      leaveRoom(c);
      addPlayer(room, c, cleanName(m.name));
      broadcast(room);
      return;
    }
    case 'leave':
      leaveRoom(c);
      return;
  }
  const room = c.room;
  if (!room) return;
  const me = room.players.get(c.id);
  if (!me) return;
  switch (m.t) {
    case 'start':
      if (room.hostId !== c.id) { send(c, { t: 'err', m: 'Hanya host yang bisa memulai ronde.' }); return; }
      if (room.phase === 'play') return;
      startRound(room);
      return;
    case 'end':
      if (room.hostId !== c.id || room.phase !== 'play') return;
      finishRound(room);
      return;
    case 'go':
      if (room.phase !== 'play' || me.status !== 'wait') return;
      me.status = 'running';
      me.startedAt = Date.now();
      broadcast(room);
      return;
    case 'stop': {
      if (room.phase !== 'play' || me.status !== 'running') return;
      const elapsed = Date.now() - me.startedAt;
      let ms = Math.floor(Number(m.ms));
      if (!Number.isFinite(ms) || ms < 0 || ms > MAX_MS || Math.abs(ms - elapsed) > SKEW_MS) ms = Math.min(elapsed, MAX_MS);
      me.ms = ms;
      me.n = dexFromMs(ms);
      me.diff = Math.abs(me.n - room.target);
      me.status = 'done';
      if (allDone(room)) finishRound(room); else broadcast(room);
      return;
    }
  }
}

httpServer.listen(PORT, () => {
  console.log('Pokédex Stopwatch berjalan di http://localhost:' + PORT);
});

process.on('SIGTERM', () => { for (const c of clients) c.close(1001); httpServer.close(() => process.exit(0)); setTimeout(() => process.exit(0), 2000).unref(); });
