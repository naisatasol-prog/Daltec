// Nube Daltec DAL-1P-EX — Express + MongoDB (base daltec_db). Variables: MONGODB_URI, DB_NAME, JWT_SECRET, PORT
const express = require('express');
const bcrypt = require('bcryptjs');
const jwt = require('jsonwebtoken');
const crypto = require('crypto');
const { MongoClient } = require('mongodb');
const { EventEmitter } = require('events');

const { MONGODB_URI, JWT_SECRET } = process.env;
const DB_NAME = process.env.DB_NAME || 'daltec_db';
const PORT = Number(process.env.PORT) || 3000;   // Render asigna el puerto en PORT
if (!MONGODB_URI || !JWT_SECRET) { console.error('Faltan MONGODB_URI o JWT_SECRET'); process.exit(1); }

const MODELS = ['DAL-1P-EX', 'DAL-LECTOR'];
const SERIAL_RE = /^DAL-(\d{8}|L[0-9A-F]{8})$/;   // relé: DAL-########  ·  lector: DAL-L + 8 hex
const LIM = { p: 100, g: 8, s: 8 };
const ONLINE_MS = 45000;
const UNCL_TTL = 7 * 864e5;

let users, devices, events;
let ready = false;                       // la base de datos aún no está lista -> 503 rápido (en vez de dejar la petición colgada)
const wake = new EventEmitter(); wake.setMaxListeners(0);   // despierta los sondeos largos de un equipo cuando hay una orden o una edición
const app = express();
app.set('trust proxy', 1);
app.disable('x-powered-by');
// CORS abierto: la autenticación va por token Bearer (no por cookies), así que cualquier origen
// (file://, localhost, GitHub Pages...) puede usar la API sin riesgo de CSRF.
app.use((req, res, next) => {
  res.set({ 'Access-Control-Allow-Origin': '*', 'Access-Control-Allow-Headers': 'Authorization, Content-Type',
    'Access-Control-Allow-Methods': 'GET, POST, DELETE, OPTIONS', 'Access-Control-Max-Age': '86400' });
  if (req.method === 'OPTIONS') return res.sendStatus(204);
  next();
});
app.use((req, res, next) => {
  if (ready || req.path === '/healthz' || req.path === '/') return next();
  res.status(503).set('Retry-After', '3').type('text').send('STARTING\n');
});
app.use(express.urlencoded({ extended: false, limit: '16kb' }));
app.use(express.json({ limit: '16kb' }));
app.use('/api/device', express.text({ type: '*/*', limit: '64kb' }));

// ---------- utilidades ----------
const wrap = fn => (req, res, next) => Promise.resolve(fn(req, res, next)).catch(next);
const fail = (res, code, msg) => res.status(code).json({ error: msg });
const clean = (s, max = 23) => String(s == null ? '' : s).replace(/[\u0000-\u001f\u007f"\\|<>&]/g, '').trim().slice(0, max);
const int = (v, d = NaN) => { const n = Number.parseInt(v, 10); return Number.isFinite(n) ? n : d; };
const sha = s => crypto.createHash('sha256').update(String(s)).digest();
const safeEq = (a, b) => crypto.timingSafeEqual(sha(a), sha(b));
const nowS = () => Math.floor(Date.now() / 1000);
const fnu = async (p) => { const r = await p; return r && Object.prototype.hasOwnProperty.call(r, 'value') && r.ok !== undefined ? r.value : r; };
const blank = () => ({ rev: 0, people: [], groups: [], scheds: [], cmds: [], mode: 0, relay: 0, ip: '', rssi: 0, fw: '', lastSeen: null, lastCard: 0, devTs: 0, devName: '' });

// ---------- usuarios ----------
const tries = new Map();
setInterval(() => { const t = Date.now(); for (const [k, v] of tries) if (t - v.t > 9e5) tries.delete(k); }, 6e4).unref();
function limited(key) { const v = tries.get(key); return v && Date.now() - v.t < 9e5 && v.n >= 8; }
function bump(key) { const v = tries.get(key); if (!v || Date.now() - v.t >= 9e5) tries.set(key, { n: 1, t: Date.now() }); else v.n++; }
const makeToken = uid => jwt.sign({ uid: String(uid) }, JWT_SECRET, { expiresIn: '7d' });
const needUser = wrap(async (req, res, next) => {
  try { const m = /^Bearer (.+)$/.exec(req.get('Authorization') || ''); const p = jwt.verify(m ? m[1] : '', JWT_SECRET); req.uid = p.uid; next(); }
  catch (e) { fail(res, 401, 'Sesión no válida'); }
});
const EMAIL_RE = /^[^\s@]{1,64}@[^\s@]{1,190}\.[^\s@]{2,}$/;

app.post('/api/auth/register', wrap(async (req, res) => {
  const email = clean(req.body.email, 254).toLowerCase(), pw = String(req.body.password || '');
  if (!EMAIL_RE.test(email)) return fail(res, 400, 'Correo no válido');
  if (pw.length < 8 || pw.length > 72) return fail(res, 400, 'La contraseña debe tener de 8 a 72 caracteres');
  try {
    const r = await users.insertOne({ email, hash: await bcrypt.hash(pw, 10), created: new Date() });
    res.json({ ok: true, email, token: makeToken(r.insertedId) });
  } catch (e) { if (e.code === 11000) return fail(res, 409, 'Ese correo ya está registrado'); throw e; }
}));
app.post('/api/auth/login', wrap(async (req, res) => {
  const email = clean(req.body.email, 254).toLowerCase(), pw = String(req.body.password || '');
  const key = req.ip + '|' + email;
  if (limited(key)) return fail(res, 429, 'Demasiados intentos. Espera 15 minutos.');
  const u = await users.findOne({ email });
  if (!u || !(await bcrypt.compare(pw, u.hash))) { bump(key); return fail(res, 401, 'Correo o contraseña incorrectos'); }
  tries.delete(key); res.json({ ok: true, email, token: makeToken(u._id) });
}));
app.post('/api/auth/logout', (req, res) => res.json({ ok: true }));   // el cliente descarta su token
app.get('/api/auth/me', needUser, wrap(async (req, res) => {
  const { ObjectId } = require('mongodb');
  const u = await users.findOne({ _id: new ObjectId(req.uid) });
  if (!u) return fail(res, 401, 'Sesión no válida');
  res.json({ email: u.email });
}));

// ---------- equipos del usuario ----------
const isOnline = d => d.lastSeen && Date.now() - new Date(d.lastSeen).getTime() < ONLINE_MS;
app.get('/api/devices', needUser, wrap(async (req, res) => {
  const l = await devices.find({ owner: req.uid }).sort({ serial: 1 }).toArray();
  res.json(l.map(d => ({ model: d.model, serial: d.serial, name: d.label || d.devName || d.serial, online: !!isOnline(d), ip: d.ip || '' })));
}));
app.post('/api/devices', needUser, wrap(async (req, res) => {
  const model = clean(req.body.model, 20), serial = clean(req.body.serial, 20).toUpperCase(), name = clean(req.body.name);
  if (!MODELS.includes(model)) return fail(res, 400, 'Modelo no soportado');
  if (!SERIAL_RE.test(serial)) return fail(res, 400, 'Número de serie no válido (DAL-######## o DAL-L########)');
  try {
    await devices.findOneAndUpdate({ serial, owner: null },
      { $set: { owner: req.uid, model, label: name || serial, claimedAt: new Date() }, $unset: { exp: '' }, $setOnInsert: { secret: null, ...blank() } },
      { upsert: true });
    res.json({ ok: true, serial });
  } catch (e) {
    if (e.code === 11000) {
      const d = await devices.findOne({ serial });
      return fail(res, 409, d && d.owner === req.uid ? 'Ese equipo ya está en tu cuenta' : 'Ese equipo ya está registrado en otra cuenta');
    }
    throw e;
  }
}));
app.delete('/api/devices/:serial', needUser, wrap(async (req, res) => {
  const serial = req.params.serial;
  const r = await devices.updateOne({ serial, owner: req.uid },
    { $set: { owner: null, label: '', ...blank(), exp: new Date(Date.now() + UNCL_TTL) } });
  if (!r.matchedCount) return fail(res, 404, 'No existe');
  await events.deleteMany({ serial });
  res.json({ ok: true });
}));

// ---------- panel por equipo (/api/d/:serial/...) ----------
const own = wrap(async (req, res, next) => {
  const d = await devices.findOne({ serial: req.params.serial, owner: req.uid });
  if (!d) return fail(res, 404, 'Equipo no encontrado');
  req.dev = d; next();
});
const R = express.Router({ mergeParams: true });
app.use('/api/d/:serial', needUser, own, R);

R.get('/status', (req, res) => {
  const d = req.dev;
  res.json({ serial: d.serial, model: d.model, name: d.label || d.devName || d.serial, mode: d.mode, relay: d.relay, ip: d.ip, rssi: d.rssi, fw: d.fw,
    online: !!isOnline(d), lastSeen: d.lastSeen ? Math.floor(new Date(d.lastSeen).getTime() / 1000) : 0, lastCard: d.lastCard || 0, time: d.devTs || 0, rev: d.rev, pending: (d.cmds || []).length });
});
R.post('/door', wrap(async (req, res) => {
  const cmd = String(req.body.cmd || '');
  if (!['pulse', 'open', 'closed', 'auto'].includes(cmd)) return fail(res, 400, 'Comando inválido');
  const id = crypto.randomInt(1, 2e9);
  await devices.updateOne({ serial: req.dev.serial }, { $push: { cmds: { $each: [{ id, cmd, at: Date.now() }], $slice: -8 } } });
  wake.emit(req.dev.serial);   // si el equipo tiene un sondeo largo abierto, recibe la orden al instante
  res.json({ ok: true, online: !!isOnline(req.dev) });
}));
R.get('/list', (req, res) => {
  const d = req.dev, t = req.query.t;
  if (t === 'p') return res.json(d.people);
  if (t === 'g') return res.json(d.groups);
  if (t === 's') return res.json(d.scheds);
  fail(res, 400, 'Tipo inválido');
});
R.get('/events', wrap(async (req, res) => {
  const l = await events.find({ serial: req.dev.serial }).sort({ rcv: -1, seq: -1 }).limit(100).toArray();
  res.json(l.map(e => ({ seq: e.seq, ts: e.ts || Math.floor(e.rcv.getTime() / 1000), t: e.t, who: e.who })));
}));

// modifica people/groups/scheds con control de concurrencia por rev
async function mutate(serial, fn) {
  for (let i = 0; i < 4; i++) {
    const d = await devices.findOne({ serial });
    if (!d) throw Object.assign(new Error('Equipo no encontrado'), { http: 404 });
    const nd = { people: d.people.map(x => ({ ...x })), groups: d.groups.map(x => ({ ...x })), scheds: d.scheds.map(x => ({ ...x })) };
    const out = fn(nd);
    const r = await devices.updateOne({ serial, rev: d.rev }, { $set: nd, $inc: { rev: 1 } });
    if (r.matchedCount) { wake.emit(serial); return out; }
  }
  throw Object.assign(new Error('Conflicto de edición, intenta de nuevo'), { http: 409 });
}
const bad = (code, msg) => Object.assign(new Error(msg), { http: code });
const freeId = (arr, max) => { for (let i = 0; i < max; i++) if (!arr.some(x => x.id === i)) return i; return -1; };

R.post('/save', wrap(async (req, res) => {
  const b = req.body, t = b.t, name = clean(b.name);
  let id = b.id === undefined || b.id === '' ? -1 : int(b.id, -1);
  if (!name) return fail(res, 400, 'Falta el nombre');
  const out = await mutate(req.dev.serial, nd => {
    const arr = t === 'p' ? nd.people : t === 'g' ? nd.groups : t === 's' ? nd.scheds : null;
    if (!arr) throw bad(400, 'Tipo inválido');
    let item;
    if (t === 'p') {
      if (!/^\d{1,10}$/.test(String(b.card || ''))) throw bad(400, 'Tarjeta inválida');
      const card = Number(b.card); if (card > 0xFFFFFFFF) throw bad(400, 'Tarjeta fuera de rango');
      const group = int(b.group, 255);
      if (group !== 255 && !nd.groups.some(g => g.id === group)) throw bad(400, 'Grupo inválido');
      if (nd.people.some(p => p.card === card && p.id !== id)) throw bad(409, 'Esa tarjeta ya está registrada');
      item = { name, card, group, en: int(b.en, 0) ? 1 : 0 };
    } else if (t === 'g') {
      const sched = int(b.sched, 255);
      if (sched !== 255 && !nd.scheds.some(s => s.id === sched)) throw bad(400, 'Horario inválido');
      item = { name, sched };
    } else {
      const days = int(b.days), from = int(b.from), to = int(b.to);
      if (!(days >= 0 && days <= 127 && from >= 0 && from <= 1439 && to >= 0 && to <= 1439)) throw bad(400, 'Datos inválidos');
      item = { name, days, from, to };
    }
    if (id < 0) { id = freeId(arr, LIM[t]); if (id < 0) throw bad(409, 'Límite alcanzado (' + LIM[t] + ')'); arr.push({ id, ...item }); }
    else { const i = arr.findIndex(x => x.id === id); if (i < 0) throw bad(404, 'No existe'); arr[i] = { id, ...item }; }
    return id;
  });
  res.json({ ok: true, id: out });
}));
R.post('/del', wrap(async (req, res) => {
  const t = req.body.t, id = int(req.body.id, -1);
  await mutate(req.dev.serial, nd => {
    const key = t === 'p' ? 'people' : t === 'g' ? 'groups' : t === 's' ? 'scheds' : null;
    if (!key) throw bad(400, 'Tipo inválido');
    if (!nd[key].some(x => x.id === id)) throw bad(404, 'No existe');
    if (t === 'g' && nd.people.some(p => p.group === id)) throw bad(409, 'El grupo está en uso por personas');
    if (t === 's' && nd.groups.some(g => g.sched === id)) throw bad(409, 'El horario está en uso por grupos');
    nd[key] = nd[key].filter(x => x.id !== id);
  });
  res.json({ ok: true });
}));

// ---------- equipo ↔ nube ----------
const deviceAuth = wrap(async (req, res, next) => {
  const serial = String(req.get('X-Serial') || ''), model = String(req.get('X-Model') || ''), key = String(req.get('X-Key') || '');
  if (!SERIAL_RE.test(serial) || !MODELS.includes(model) || !/^[0-9a-f]{32}$/.test(key)) return res.status(400).type('text').send('BAD\n');
  let d = await devices.findOne({ serial });
  if (!d) {
    try { await devices.insertOne({ serial, model, owner: null, label: '', secret: key, exp: new Date(Date.now() + UNCL_TTL), ...blank() }); }
    catch (e) { if (e.code !== 11000) throw e; }
    d = await devices.findOne({ serial });
  } else if (!d.secret) {
    await devices.updateOne({ serial, $or: [{ secret: null }, { secret: { $exists: false } }] }, { $set: { secret: key } });
    d = await devices.findOne({ serial });
  } else if (!d.owner && !safeEq(d.secret, key)) {
    // Equipo sin dueño (desvinculado o restablecido de fábrica): acepta su clave nueva.
    await devices.updateOne({ serial, owner: null }, { $set: { secret: key } });
    d = await devices.findOne({ serial });
  }
  if (!d || !d.secret || !safeEq(d.secret, key)) return res.status(403).type('text').send('FORBIDDEN\n');
  req.dev = d; next();
});
const lines = body => String(body || '').split('\n').map(l => l.replace(/\r$/, '')).filter(Boolean).map(l => l.split('|'));

function parseSnapshot(ls) {
  const o = { scheds: [], groups: [], people: [] };
  for (const f of ls) {
    if (f[0] === 'S' && f.length >= 6 && int(f[1], -1) >= 0 && int(f[1]) < LIM.s) o.scheds.push({ id: int(f[1]), name: clean(f[2]), days: int(f[3], 127) & 127, from: Math.min(1439, Math.max(0, int(f[4], 0))), to: Math.min(1439, Math.max(0, int(f[5], 1439))) });
    else if (f[0] === 'G' && f.length >= 4 && int(f[1], -1) >= 0 && int(f[1]) < LIM.g) o.groups.push({ id: int(f[1]), name: clean(f[2]), sched: int(f[3], 255) });
    else if (f[0] === 'P' && f.length >= 6 && int(f[1], -1) >= 0 && int(f[1]) < LIM.p) o.people.push({ id: int(f[1]), name: clean(f[2]), card: Math.min(0xFFFFFFFF, Math.max(0, Number(f[3]) || 0)), group: int(f[4], 255), en: int(f[5], 0) ? 1 : 0 });
  }
  return o;
}

// Espera hasta 'ms' a que haya algo para el equipo. Devuelve el documento actualizado, o null si el equipo cortó la conexión.
function waitChange(serial, ms, base, res) {
  return new Promise((resolve, reject) => {
    let fin = false, t1, t2;
    const end = async alive => {
      if (fin) return; fin = true; clearTimeout(t1); clearInterval(t2); wake.off(serial, onWake); res.off('close', onClose);
      if (!alive) return resolve(null);
      try { resolve(await devices.findOne({ serial })); } catch (e) { reject(e); }
    };
    const onWake = () => end(true);
    const onClose = () => { if (!res.writableEnded) end(false); };
    wake.on(serial, onWake); res.on('close', onClose);
    t1 = setTimeout(() => end(true), ms);
    t2 = setInterval(async () => {                      // respaldo por si la orden la atendió otra instancia del servidor: revisa la base cada 4 s
      try { const x = await devices.findOne({ serial }, { projection: { cmds: 1, rev: 1, owner: 1 } }); if (x && (!x.owner || (x.cmds || []).length || x.rev !== base.rev)) end(true); } catch (e) { /* se reintenta */ }
    }, 4000);
  });
}
app.post('/api/device/poll', deviceAuth, wrap(async (req, res) => {
  const d = req.dev, ls = lines(req.body), H = ls.find(f => f[0] === 'H') || [];
  const txt = s => clean(s, 40);
  const set = { lastSeen: new Date(), mode: Math.min(2, Math.max(0, int(H[3], 0))), relay: int(H[4], 0) ? 1 : 0, ip: txt(H[5]), rssi: int(H[6], 0), fw: txt(H[7]),
    devTs: int(H[8], 0), lastCard: Math.max(0, Number(H[9]) || 0), devName: txt(H[10]) };
  if (!d.owner) {
    await devices.updateOne({ serial: d.serial }, { $set: { ...set, exp: new Date(Date.now() + UNCL_TTL) } });
    return res.type('text').send('UNCLAIMED\n');
  }
  // eventos
  const boot = txt(H[11]);
  const evs = ls.filter(f => f[0] === 'E' && f.length >= 5 && 'ADURBMWL'.includes(f[3][0] || '-')).slice(0, 20)
    .map(f => ({ serial: d.serial, boot, seq: int(f[1], 0), ts: int(f[2], 0), t: f[3][0], who: clean(f[4], 28), rcv: new Date() }));
  if (evs.length) { try { await events.insertMany(evs, { ordered: false }); } catch (e) { if (e.code !== 11000 && !(e.writeErrors || []).every(w => w.code === 11000)) throw e; } }
  const acks = ls.filter(f => f[0] === 'K').map(f => int(f[1], -1));
  const upd = { $set: set, $pull: { cmds: { $or: [{ id: { $in: acks } }, { at: { $lt: Date.now() - 6e5 } }] } } };
  const push = int(H[2], 0) === 1;
  if (push) Object.assign(upd.$set, parseSnapshot(ls)), upd.$inc = { rev: 1 };
  const nd = await fnu(devices.findOneAndUpdate({ serial: d.serial, owner: d.owner }, upd, { returnDocument: 'after' }));
  if (!nd) return res.type('text').send('UNCLAIMED\n');
  // Sondeo largo (?wait=N): si no hay nada que entregar, se retiene la petición hasta N s (máx. 20) y se responde AL INSTANTE cuando llega
  // una orden o una edición desde la web. Sin ?wait responde de inmediato (el relé en modo respaldo y firmwares viejos siguen igual).
  let cur = nd;
  const waitS = Math.min(20, Math.max(0, int(req.query.wait, 0)));
  if (waitS && !push && !(nd.cmds || []).length && int(H[1], -1) === nd.rev) {
    cur = await waitChange(d.serial, waitS * 1000, nd, res);
    if (!cur) return;                                   // el equipo cortó la conexión
    if (!cur.owner) return res.type('text').send('UNCLAIMED\n');
  }
  let out = `OK|${cur.rev}|${nowS()}\n`;
  if (push) out += 'PUSHED\n';
  for (const c of (cur.cmds || []).slice(0, 4)) out += `CMD|${c.id}|${c.cmd}\n`;
  res.type('text').send(out);
}));

// El equipo pide desvincularse (al restablecer de fábrica): queda libre para otra cuenta.
app.post('/api/device/unlink', deviceAuth, wrap(async (req, res) => {
  const d = req.dev;
  if (d.owner) {
    await devices.updateOne({ serial: d.serial, owner: d.owner },
      { $set: { owner: null, label: '', ...blank(), exp: new Date(Date.now() + UNCL_TTL) } });
    await events.deleteMany({ serial: d.serial });
  }
  res.type('text').send('OK\n');
}));

app.get('/api/device/db', deviceAuth, (req, res) => {
  const d = req.dev;
  if (!d.owner) return res.status(404).type('text').send('UNCLAIMED\n');
  let o = `V|${d.rev}\n`;
  for (const s of d.scheds) o += `S|${s.id}|${s.name}|${s.days}|${s.from}|${s.to}\n`;
  for (const g of d.groups) o += `G|${g.id}|${g.name}|${g.sched}\n`;
  for (const p of d.people) o += `P|${p.id}|${p.name}|${p.card}|${p.group}|${p.en}\n`;
  res.type('text').send(o + 'END\n');
});

// ---------- raíz y errores (el servidor ya NO sirve archivos estáticos) ----------
app.get('/healthz', (req, res) => res.send('ok'));
app.get('/', (req, res) => res.json({ service: 'daltec-cloud', ok: true }));
app.use('/api', (req, res) => fail(res, 404, 'Ruta no encontrada'));
app.use((err, req, res, next) => {
  if (err && err.http) return fail(res, err.http, err.message);
  console.error(err);
  fail(res, 500, 'Error del servidor');
});

// Se escucha YA (Render ve el puerto abierto en segundos y el equipo recibe 503 rápido en vez de una petición colgada) y la base se conecta en segundo plano.
const srv = app.listen(PORT, '0.0.0.0', () => console.log(`Daltec nube escuchando en :${PORT} (db ${DB_NAME})`));
srv.keepAliveTimeout = 65000; srv.headersTimeout = 66000;   // mayores que los del proxy de Render (evita 502 por conexiones reutilizadas)
(async function boot() {
  for (;;) {
    const client = new MongoClient(MONGODB_URI, { serverSelectionTimeoutMS: 8000 });
    try {
      await client.connect();
      const db = client.db(DB_NAME);
      users = db.collection('users'); devices = db.collection('devices'); events = db.collection('events');
      await Promise.all([
        users.createIndex({ email: 1 }, { unique: true }),
        devices.createIndex({ serial: 1 }, { unique: true }),
        devices.createIndex({ owner: 1 }),
        devices.createIndex({ exp: 1 }, { expireAfterSeconds: 0 }),
        events.createIndex({ serial: 1, boot: 1, seq: 1 }, { unique: true }),
        events.createIndex({ rcv: 1 }, { expireAfterSeconds: 90 * 86400 })
      ]);
      ready = true; console.log('Base de datos lista');
      return;
    } catch (e) {
      console.error('Fallo al conectar la base:', e.message, '- reintento en 5 s');
      client.close().catch(() => {});
      await new Promise(r => setTimeout(r, 5000));
    }
  }
})();
