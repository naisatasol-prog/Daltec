'use strict';
/**
 * CONTROL DE AIRES — API v2 (multi-cliente, MongoDB Atlas)
 * Variables de entorno: MONGODB_URI, JWT_SECRET, ADMIN_TOKEN, DEVICE_KEY, ALLOWED_ORIGIN, APP_TIMEZONE, POLL_SECONDS.
 *
 * El contrato con el ESP-01 NO cambió: POST /api/devices/:id/status con x-device-key, misma respuesta.
 * Propiedad de equipos: el ID del dispositivo grabado en el ESP debe empezar con el ID de la cuenta
 * (ej. CLI-0001AB-oficina1). Así cada cliente solo puede dar de alta sus propios equipos.
 * Estados: "ON"/"OFF". Días: 0 = domingo ... 6 = sábado.
 */
const express = require('express');
const cors = require('cors');
const cron = require('node-cron');
const crypto = require('crypto');
const mongo = require('./db');

const clamp = (n, a, b) => Math.min(b, Math.max(a, n));
const PORT = Number(process.env.PORT) || 3000;
const ADMIN_TOKEN = process.env.ADMIN_TOKEN || '';
const DEVICE_KEY = process.env.DEVICE_KEY || '';
const JWT_SECRET = process.env.JWT_SECRET || '';
const APP_TIMEZONE = process.env.APP_TIMEZONE || 'America/Mexico_City';
const POLL_SECONDS = clamp(Number(process.env.POLL_SECONDS) || 10, 3, 120);
const ALLOWED_ORIGIN = process.env.ALLOWED_ORIGIN || '*';
const TOKEN_DAYS = 7;
const LIM = { branches: 50, zones: 100, devices: 200, routines: 100 };
const ID_RE = /^[a-z0-9][a-z0-9_-]{0,39}$/i;
const TIME_RE = /^([01]\d|2[0-3]):[0-5]\d$/;
const EMAIL_RE = /^[^\s@]+@[^\s@]+\.[^\s@]+$/;
const TYPES = ['Edificio', 'Parque', 'Casa', 'Otro'];

class HttpError extends Error { constructor(status, message) { super(message); this.status = status; } }
const wrap = (fn) => (req, res, next) => Promise.resolve(fn(req, res, next)).catch(next);
const col = (n) => mongo.col(n);
const rid = () => crypto.randomBytes(5).toString('hex');
const safeEqual = (a, b) => { const A = Buffer.from(String(a)); const B = Buffer.from(String(b)); return A.length === B.length && crypto.timingSafeEqual(A, B); };
const text = (v, max, label) => { const s = String(v ?? '').trim(); if (!s || s.length > max) throw new HttpError(400, `${label} debe tener entre 1 y ${max} caracteres`); return s; };
const parseState = (v) => { const s = String(v || '').toUpperCase(); if (s !== 'ON' && s !== 'OFF') throw new HttpError(400, 'El estado debe ser "ON" u "OFF"'); return s; };

/* ---------- Sesiones y contraseñas (sin dependencias extra) ---------- */
function sign(sub) {
  const p = Buffer.from(JSON.stringify({ sub, exp: Date.now() + TOKEN_DAYS * 864e5 })).toString('base64url');
  return `${p}.${crypto.createHmac('sha256', JWT_SECRET).update(p).digest('base64url')}`;
}
function verify(token) {
  const [p, s] = String(token).split('.');
  if (!p || !s || !safeEqual(s, crypto.createHmac('sha256', JWT_SECRET).update(p).digest('base64url'))) return null;
  try { const o = JSON.parse(Buffer.from(p, 'base64url')); return o.exp > Date.now() ? o.sub : null; } catch { return null; }
}
const hashPw = (pw) => new Promise((ok, no) => { const salt = crypto.randomBytes(16); crypto.scrypt(pw, salt, 64, (e, k) => (e ? no(e) : ok(`${salt.toString('hex')}:${k.toString('hex')}`))); });
const checkPw = (pw, stored) => new Promise((ok) => { const [s, h] = String(stored).split(':'); if (!s || !h) return ok(false); crypto.scrypt(pw, Buffer.from(s, 'hex'), 64, (e, k) => ok(!e && safeEqual(k.toString('hex'), h))); });

const attempts = new Map(); // límite simple contra adivinar contraseñas
function tooMany(key) { const a = attempts.get(key); return Boolean(a && a.reset > Date.now() && a.n >= 10); }
function failed(key) { const a = attempts.get(key); if (a && a.reset > Date.now()) a.n += 1; else attempts.set(key, { n: 1, reset: Date.now() + 15 * 60e3 }); }

const requireUser = wrap(async (req, res, next) => {
  const h = req.get('authorization') || '';
  const sub = h.startsWith('Bearer ') ? verify(h.slice(7)) : null;
  const acc = sub && (await col('accounts').findOne({ _id: sub }));
  if (!acc) return res.status(401).json({ error: 'Sesión no válida. Inicia sesión de nuevo.' });
  req.acc = acc;
  next();
});
const requireAdmin = (req, res, next) => {
  const h = req.get('authorization') || '';
  if (!ADMIN_TOKEN || !safeEqual(h.startsWith('Bearer ') ? h.slice(7) : '', ADMIN_TOKEN)) return res.status(401).json({ error: 'Token de administrador incorrecto' });
  next();
};
const requireDevice = (req, res, next) => {
  if (!DEVICE_KEY || !safeEqual(req.get('x-device-key') || '', DEVICE_KEY)) return res.status(401).json({ error: 'Clave de dispositivo incorrecta' });
  next();
};
const pubAccount = (a) => ({ id: a._id, email: a.email, company: a.company, color: a.color, logo: a.logo });

/* ---------- Dispositivos: en memoria (ruta rápida del ESP) + guardado en MongoDB ---------- */
const devices = new Map();
const dirty = new Set();
let flushTimer = null;

const newDevice = (id, state) => ({ id, accountId: null, name: id, model: '', branchId: null, zoneId: null, desiredState: state, reportedState: state,
  lastSeen: null, rssi: null, fw: null, hwModel: null, serial: null, cmdAt: null, ssid: null, wifiStatus: null, pendingWifi: null });
const isOnline = (d) => Boolean(d.lastSeen) && Date.now() - Date.parse(d.lastSeen) < Math.max(30, POLL_SECONDS * 3) * 1000;
const toPublic = (d) => ({ id: d.id, name: d.name, model: d.model, branchId: d.branchId, zoneId: d.zoneId, desiredState: d.desiredState, reportedState: d.reportedState,
  online: isOnline(d), lastSeen: d.lastSeen, rssi: d.rssi, fw: d.fw, hwModel: d.hwModel, serial: d.serial, ssid: d.ssid, wifiStatus: d.wifiStatus });

function persist(d) { dirty.add(d.id); clearTimeout(flushTimer); flushTimer = setTimeout(flush, 300); }
async function flush() {
  const ids = [...dirty]; dirty.clear();
  if (!ids.length) return;
  const ops = ids.filter((id) => devices.has(id)).map((id) => { const { pendingWifi, ...doc } = devices.get(id); return { replaceOne: { filter: { _id: id }, replacement: doc, upsert: true } }; });
  try { if (ops.length) await col('devices').bulkWrite(ops); } catch (err) { console.error('[mongo] Error al guardar equipos:', err.message); ids.forEach((i) => dirty.add(i)); }
}
function release(d) { // el equipo deja la cuenta pero sigue existiendo (si el ESP está encendido, reaparece sin dueño)
  Object.assign(d, { accountId: null, branchId: null, zoneId: null, model: '', name: d.id, desiredState: d.reportedState, pendingWifi: null });
  persist(d);
}
const ownerOf = (id, accounts) => accounts.find((a) => id.toUpperCase().startsWith(`${a._id.toUpperCase()}-`));
const mine = (req) => { const d = devices.get(req.params.id); if (!d || d.accountId !== req.acc._id) throw new HttpError(404, 'No existe un equipo con ese ID en tu cuenta'); return d; };

/* ---------- Wi-Fi (igual que antes) ---------- */
const wifiBusy = (d) => Boolean(d.wifiStatus) && (d.wifiStatus.state === 'pending' || d.wifiStatus.state === 'sent');
function applyWifiResult(d, r) {
  if ((r !== 'ok' && r !== 'failed') || !wifiBusy(d)) return false;
  d.wifiStatus = { ...d.wifiStatus, state: r, at: new Date().toISOString() }; d.pendingWifi = null; return true;
}

/* ---------- Validación de rutinas ---------- */
function cleanRoutine(b, branch) {
  const t = (v) => { if (v === null || v === undefined || v === '') return null; if (typeof v !== 'string' || !TIME_RE.test(v)) throw new HttpError(400, 'La hora debe tener formato HH:MM (24 h)'); return v; };
  const onTime = t(b.onTime), offTime = t(b.offTime);
  if (!onTime && !offTime) throw new HttpError(400, 'Define al menos una hora (encendido o apagado)');
  if (onTime && onTime === offTime) throw new HttpError(400, 'La hora de encendido y apagado no pueden ser iguales');
  const days = [...new Set((Array.isArray(b.days) ? b.days : []).map(Number))];
  if (!days.length || days.some((n) => !Number.isInteger(n) || n < 0 || n > 6)) throw new HttpError(400, 'Elige al menos un día (0 = domingo ... 6 = sábado)');
  const zoneId = b.zoneId || null;
  if (zoneId && !branch.zones.some((z) => z.id === zoneId)) throw new HttpError(400, 'La zona no pertenece a esa sucursal');
  return { branchId: branch._id, zoneId, onTime, offTime, days: days.sort((x, y) => x - y), enabled: b.enabled !== false };
}
const pubRoutine = ({ _id, accountId, ...r }) => ({ id: _id, ...r });

/* Horarios que se mandan al ESP para que los guarde en su flash (formato "enc,apa,dias;..."; minutos desde 00:00, dias = máscara bit0=domingo). */
const routineCache = new Map();
async function routinesOf(accountId) {
  const c = routineCache.get(accountId);
  if (c && Date.now() - c.at < 15000) return c.list;
  const list = await col('routines').find({ accountId, enabled: true }).toArray();
  routineCache.set(accountId, { at: Date.now(), list });
  return list;
}
const bustRoutines = (accountId) => routineCache.delete(accountId);
const toMin = (hhmm) => { if (!hhmm) return -1; const [h, m] = String(hhmm).split(':').map(Number); return h * 60 + m; };
async function schedFor(d) {
  if (!d.accountId || !d.branchId) return '';
  const list = (await routinesOf(d.accountId)).filter((r) => r.branchId === d.branchId && (!r.zoneId || r.zoneId === d.zoneId));
  return list.slice(0, 12).map((r) => `${toMin(r.onTime)},${toMin(r.offTime)},${r.days.reduce((m, x) => m | (1 << x), 0)}`).join(';');
}
function localClock(date = new Date()) { // día de la semana y segundos desde las 00:00 en APP_TIMEZONE
  const parts = new Intl.DateTimeFormat('en-US', { timeZone: APP_TIMEZONE, weekday: 'short', hour: '2-digit', minute: '2-digit', second: '2-digit', hourCycle: 'h23' }).formatToParts(date);
  const g = (t) => parts.find((p) => p.type === t).value;
  return { day: WEEKDAYS[g('weekday')], secs: Number(g('hour')) * 3600 + Number(g('minute')) * 60 + Number(g('second')) };
}
const pubBranch = (b) => ({ id: b._id, name: b.name, type: b.type, zones: b.zones });
async function myBranch(req, id) { const b = await col('branches').findOne({ _id: String(id || ''), accountId: req.acc._id }); if (!b) throw new HttpError(404, 'Sucursal no encontrada'); return b; }

/* ---------- App ---------- */
const app = express();
app.disable('x-powered-by');
app.set('trust proxy', 1);
const ORIGINS = ALLOWED_ORIGIN.split(',').map((s) => s.trim()).filter(Boolean);
const LOCAL_RE = /^https?:\/\/(localhost|127\.0\.0\.1)(:\d+)?$/;
// Permite: '*', los orígenes de ALLOWED_ORIGIN, localhost (pruebas) y "null" (index.html abierto con doble clic).
// La API usa Bearer token (no cookies), así que esto no expone sesiones.
const corsOrigin = (origin, cb) => cb(null, !origin || ORIGINS.includes('*') || ORIGINS.includes(origin) || LOCAL_RE.test(origin) || origin === 'null');
app.use(cors({ origin: corsOrigin,
  methods: ['GET', 'POST', 'PUT', 'PATCH', 'DELETE', 'OPTIONS'], allowedHeaders: ['Content-Type', 'Authorization'] }));
const small = express.json({ limit: '20kb' });
const big = express.json({ limit: '400kb' }); // solo para el logo en PATCH /api/me
app.use((req, res, next) => (req.method === 'PATCH' && req.path === '/api/me' ? big : small)(req, res, next));

app.get('/', (req, res) => res.json({ ok: true, service: 'ac-control-api', version: 2 }));
app.get('/health', (req, res) => res.type('text').send('ok'));

/* Cuentas */
app.post('/api/auth/register', wrap(async (req, res) => {
  const b = req.body || {};
  const email = String(b.email || '').trim().toLowerCase(), pw = String(b.password || '');
  if (!EMAIL_RE.test(email) || email.length > 120) throw new HttpError(400, 'Correo no válido');
  if (pw.length < 8 || pw.length > 100) throw new HttpError(400, 'La contraseña debe tener al menos 8 caracteres');
  if (await col('accounts').findOne({ email })) throw new HttpError(409, 'Ese correo ya tiene una cuenta');
  const r = await col('counters').findOneAndUpdate({ _id: 'accounts' }, { $inc: { n: 1 } }, { upsert: true, returnDocument: 'after' });
  const n = (r && r.value ? r.value : r).n;
  const suffix = crypto.randomBytes(2).toString('hex').slice(0, 2).toUpperCase();
  const acc = { _id: `CLI-${String(n).padStart(4, '0')}${suffix}`, email, hash: await hashPw(pw), company: String(b.company || '').trim().slice(0, 60) || 'Mi empresa', color: '#2563eb', logo: '', createdAt: new Date().toISOString() };
  try { await col('accounts').insertOne(acc); } catch (e) { if (e.code === 11000) throw new HttpError(409, 'Ese correo ya tiene una cuenta'); throw e; }
  res.status(201).json({ token: sign(acc._id), account: pubAccount(acc) });
}));

app.post('/api/auth/login', wrap(async (req, res) => {
  const email = String((req.body || {}).email || '').trim().toLowerCase(), key = `${req.ip}|${email}`;
  if (tooMany(key)) throw new HttpError(429, 'Demasiados intentos. Espera unos minutos.');
  const acc = await col('accounts').findOne({ email });
  if (!acc || !(await checkPw(String((req.body || {}).password || ''), acc.hash))) { failed(key); throw new HttpError(401, 'Correo o contraseña incorrectos'); }
  attempts.delete(key);
  res.json({ token: sign(acc._id), account: pubAccount(acc) });
}));

app.patch('/api/me', requireUser, wrap(async (req, res) => {
  const b = req.body || {}, set = {};
  if (b.company !== undefined) set.company = text(b.company, 60, 'El nombre de la empresa');
  if (b.color !== undefined) { if (!/^#[0-9a-f]{6}$/i.test(b.color)) throw new HttpError(400, 'Color no válido'); set.color = b.color; }
  if (b.logo !== undefined) { if (b.logo && !/^data:image\/(png|jpeg|webp);base64,[A-Za-z0-9+/=]+$/.test(b.logo)) throw new HttpError(400, 'Logo no válido (PNG, JPG o WebP)'); if (String(b.logo).length > 300000) throw new HttpError(400, 'El logo es demasiado grande'); set.logo = b.logo; }
  if (Object.keys(set).length) await col('accounts').updateOne({ _id: req.acc._id }, { $set: set });
  res.json({ account: pubAccount({ ...req.acc, ...set }) });
}));

/* Todo el estado de la cuenta en una sola llamada (para el sondeo del panel) */
app.get('/api/state', requireUser, wrap(async (req, res) => {
  const id = req.acc._id;
  const [branches, routines] = await Promise.all([col('branches').find({ accountId: id }).toArray(), col('routines').find({ accountId: id }).toArray()]);
  res.json({
    serverTime: new Date().toISOString(), timezone: APP_TIMEZONE, pollSeconds: POLL_SECONDS, account: pubAccount(req.acc),
    branches: branches.map(pubBranch), routines: routines.map(pubRoutine),
    devices: [...devices.values()].filter((d) => d.accountId === id).sort((a, b) => a.id.localeCompare(b.id)).map(toPublic),
    detected: [],
  });
}));

/* Sucursales y zonas */
app.post('/api/branches', requireUser, wrap(async (req, res) => {
  const b = req.body || {};
  if (!TYPES.includes(b.type)) throw new HttpError(400, `El tipo debe ser: ${TYPES.join(', ')}`);
  if ((await col('branches').countDocuments({ accountId: req.acc._id })) >= LIM.branches) throw new HttpError(400, `Máximo ${LIM.branches} sucursales`);
  const doc = { _id: rid(), accountId: req.acc._id, name: text(b.name, 60, 'El nombre'), type: b.type, zones: [] };
  await col('branches').insertOne(doc);
  res.status(201).json(pubBranch(doc));
}));
app.patch('/api/branches/:id', requireUser, wrap(async (req, res) => {
  const br = await myBranch(req, req.params.id), b = req.body || {}, set = {};
  if (b.name !== undefined) set.name = text(b.name, 60, 'El nombre');
  if (b.type !== undefined) { if (!TYPES.includes(b.type)) throw new HttpError(400, 'Tipo no válido'); set.type = b.type; }
  await col('branches').updateOne({ _id: br._id }, { $set: set });
  res.json(pubBranch({ ...br, ...set }));
}));
app.delete('/api/branches/:id', requireUser, wrap(async (req, res) => {
  const br = await myBranch(req, req.params.id);
  for (const d of devices.values()) if (d.accountId === req.acc._id && d.branchId === br._id) release(d);
  await col('routines').deleteMany({ accountId: req.acc._id, branchId: br._id });
  bustRoutines(req.acc._id);
  await col('branches').deleteOne({ _id: br._id });
  res.json({ ok: true });
}));
app.post('/api/branches/:id/zones', requireUser, wrap(async (req, res) => {
  const br = await myBranch(req, req.params.id);
  if (br.zones.length >= LIM.zones) throw new HttpError(400, `Máximo ${LIM.zones} zonas por sucursal`);
  const zones = [...br.zones, { id: rid(), name: text((req.body || {}).name, 60, 'El nombre de la zona') }];
  await col('branches').updateOne({ _id: br._id }, { $set: { zones } });
  res.status(201).json(pubBranch({ ...br, zones }));
}));
app.delete('/api/branches/:id/zones/:zid', requireUser, wrap(async (req, res) => {
  const br = await myBranch(req, req.params.id);
  if (!br.zones.some((z) => z.id === req.params.zid)) throw new HttpError(404, 'Zona no encontrada');
  const zones = br.zones.filter((z) => z.id !== req.params.zid);
  await col('branches').updateOne({ _id: br._id }, { $set: { zones } });
  await col('routines').deleteMany({ accountId: req.acc._id, branchId: br._id, zoneId: req.params.zid });
  bustRoutines(req.acc._id);
  for (const d of devices.values()) if (d.accountId === req.acc._id && d.zoneId === req.params.zid) { d.zoneId = null; persist(d); }
  res.json(pubBranch({ ...br, zones }));
}));

/* Dispositivos del cliente */
async function placement(req, b) { // valida sucursal y zona de la cuenta
  if (!b.branchId) return { branchId: null, zoneId: null };
  const br = await myBranch(req, b.branchId);
  if (b.zoneId && !br.zones.some((z) => z.id === b.zoneId)) throw new HttpError(400, 'La zona no pertenece a esa sucursal');
  return { branchId: br._id, zoneId: b.zoneId || null };
}
app.post('/api/devices', requireUser, wrap(async (req, res) => {
  // Vincular un equipo a la cuenta con su NÚMERO DE SERIE (el DEVICE_ID grabado en el ESP, independiente de la cuenta).
  const b = req.body || {}, typed = String(b.id || '').trim(), key = `link|${req.acc._id}`;
  if (tooMany(key)) throw new HttpError(429, 'Demasiados intentos. Espera unos minutos.');
  if (!ID_RE.test(typed)) throw new HttpError(400, 'Número de serie inválido (letras, números, - o _; máx. 40)');
  const d = [...devices.values()].find((x) => x.id.toUpperCase() === typed.toUpperCase());
  if (!d) { failed(key); throw new HttpError(404, 'No se encontró ese número de serie. Revisa que esté bien escrito y que el equipo esté encendido y conectado a internet.'); }
  if (d.accountId === req.acc._id) throw new HttpError(409, 'Este equipo ya está en tu cuenta');
  if (d.accountId) { failed(key); throw new HttpError(409, 'Este equipo ya está vinculado a otra cuenta'); }
  if ([...devices.values()].filter((x) => x.accountId === req.acc._id).length >= LIM.devices) throw new HttpError(400, `Máximo ${LIM.devices} dispositivos`);
  const place = await placement(req, b);
  Object.assign(d, { accountId: req.acc._id, name: b.name ? text(b.name, 60, 'El nombre') : d.id, model: String(b.model || d.hwModel || '').trim().slice(0, 60), ...place });
  if (d.lastSeen) d.desiredState = d.reportedState; // se respeta el estado real del equipo
  persist(d);
  res.status(201).json(toPublic(d));
}));
app.patch('/api/devices/:id', requireUser, wrap(async (req, res) => {
  const d = mine(req), b = req.body || {};
  if (b.name !== undefined) d.name = text(b.name, 60, 'El nombre');
  if (b.model !== undefined) d.model = String(b.model).trim().slice(0, 60);
  if (b.branchId !== undefined) Object.assign(d, await placement(req, b));
  persist(d);
  res.json(toPublic(d));
}));
app.delete('/api/devices/:id', requireUser, (req, res) => { release(mine(req)); res.json({ ok: true }); });
app.post('/api/devices/:id/command', requireUser, (req, res) => { const d = mine(req); d.desiredState = parseState((req.body || {}).state); d.cmdAt = new Date().toISOString(); persist(d); res.json(toPublic(d)); });
app.post('/api/devices/:id/wifi', requireUser, (req, res) => {
  const d = mine(req), b = req.body || {}, ssid = typeof b.ssid === 'string' ? b.ssid : '', password = typeof b.password === 'string' ? b.password : '';
  const sb = Buffer.byteLength(ssid), pb = Buffer.byteLength(password);
  if (sb < 1 || sb > 32) throw new HttpError(400, 'El nombre de la red debe tener entre 1 y 32 caracteres');
  if (pb !== 0 && (pb < 8 || pb > 63)) throw new HttpError(400, 'La contraseña debe tener entre 8 y 63 caracteres (vacía solo si la red es abierta)');
  if (wifiBusy(d)) throw new HttpError(409, 'Ya hay un cambio de red en curso. Espera el resultado o cancélalo');
  d.pendingWifi = { ssid, password }; d.wifiStatus = { state: 'pending', ssid, at: new Date().toISOString() };
  persist(d); res.json(toPublic(d));
});
app.delete('/api/devices/:id/wifi', requireUser, (req, res) => {
  const d = mine(req);
  if (!wifiBusy(d)) throw new HttpError(409, 'No hay un cambio de red en curso');
  d.pendingWifi = null; d.wifiStatus = { ...d.wifiStatus, state: 'cancelled', at: new Date().toISOString() };
  persist(d); res.json(toPublic(d));
});

/* ESP-01 — contrato sin cambios. Body: { state, rssi, fw, ssidHex, wifiResult } */
app.post('/api/devices/:id/status', requireDevice, wrap(async (req, res) => {
  const id = req.params.id;
  if (!ID_RE.test(id)) throw new HttpError(400, 'ID inválido (usa letras, números, - o _; máx. 40)');
  const body = req.body || {}, reported = parseState(body.state);
  let d = devices.get(id), changed = false;
  if (!d) { d = newDevice(id, reported); devices.set(id, d); changed = true; console.log(`[devices] Equipo nuevo detectado: ${id}`); }
  if (!d.lastSeen) { d.desiredState = reported; changed = true; } // primera conexión: se adopta el estado real
  d.reportedState = reported;
  d.lastSeen = new Date().toISOString();
  // El equipo cambió de estado solo por su horario guardado mientras no había internet: se respeta, salvo que el panel haya mandado una orden más reciente.
  if (body.local === true && d.accountId && reported !== d.desiredState) {
    const ago = Number.isFinite(body.localAgo) ? clamp(body.localAgo, 0, 7 * 86400) : 0;
    if (!d.cmdAt || Date.now() - ago * 1000 > Date.parse(d.cmdAt)) { d.desiredState = reported; changed = true; }
  }
  // Identidad del equipo: modelo y número de serie (los informa el firmware)
  if (typeof body.model === 'string' && /^[\w.-]{1,32}$/.test(body.model) && body.model !== d.hwModel) { d.hwModel = body.model; changed = true; }
  if (typeof body.serial === 'string' && /^[\w.-]{1,40}$/.test(body.serial) && body.serial !== d.serial) { d.serial = body.serial; changed = true; }
  if (Number.isFinite(body.rssi)) d.rssi = body.rssi;
  if (typeof body.fw === 'string') d.fw = body.fw.slice(0, 20);
  if (typeof body.ssidHex === 'string' && /^([0-9a-f]{2}){0,32}$/i.test(body.ssidHex)) {
    const ssid = Buffer.from(body.ssidHex, 'hex').toString('utf8');
    if (ssid !== d.ssid) { d.ssid = ssid; changed = true; }
  }
  if (applyWifiResult(d, body.wifiResult)) changed = true;
  // Un equipo sin dueño nunca recibe órdenes: se queda como está.
  const reply = { desired: d.accountId ? d.desiredState : reported, pollSeconds: POLL_SECONDS, serverTime: d.lastSeen };
  if (d.accountId && d.pendingWifi) {
    reply.wifiSsidHex = Buffer.from(d.pendingWifi.ssid, 'utf8').toString('hex');
    reply.wifiPassHex = Buffer.from(d.pendingWifi.password, 'utf8').toString('hex');
    if (d.wifiStatus && d.wifiStatus.state === 'pending') { d.wifiStatus = { ...d.wifiStatus, state: 'sent', at: reply.serverTime }; changed = true; }
  }
  // Hora local + horarios de este equipo: el ESP los guarda en su flash y sigue funcionando sin internet
  const clk = localClock();
  reply.localDay = clk.day; reply.localSecs = clk.secs; reply.sched = await schedFor(d);
  if (changed) persist(d);
  res.json(reply);
}));

/* Rutinas */
app.post('/api/routines', requireUser, wrap(async (req, res) => {
  if ((await col('routines').countDocuments({ accountId: req.acc._id })) >= LIM.routines) throw new HttpError(400, `Máximo ${LIM.routines} rutinas`);
  const doc = { _id: rid(), accountId: req.acc._id, ...cleanRoutine(req.body || {}, await myBranch(req, (req.body || {}).branchId)) };
  await col('routines').insertOne(doc);
  bustRoutines(req.acc._id);
  res.status(201).json(pubRoutine(doc));
}));
app.put('/api/routines/:id', requireUser, wrap(async (req, res) => {
  const cur = await col('routines').findOne({ _id: req.params.id, accountId: req.acc._id });
  if (!cur) throw new HttpError(404, 'Rutina no encontrada');
  const doc = { ...cleanRoutine(req.body || {}, await myBranch(req, (req.body || {}).branchId)) };
  await col('routines').updateOne({ _id: cur._id }, { $set: doc });
  bustRoutines(req.acc._id);
  res.json(pubRoutine({ ...cur, ...doc }));
}));
app.patch('/api/routines/:id', requireUser, wrap(async (req, res) => {
  const cur = await col('routines').findOne({ _id: req.params.id, accountId: req.acc._id });
  if (!cur) throw new HttpError(404, 'Rutina no encontrada');
  const enabled = (req.body || {}).enabled !== false;
  await col('routines').updateOne({ _id: cur._id }, { $set: { enabled } });
  bustRoutines(req.acc._id);
  res.json(pubRoutine({ ...cur, enabled }));
}));
app.delete('/api/routines/:id', requireUser, wrap(async (req, res) => {
  const r = await col('routines').deleteOne({ _id: req.params.id, accountId: req.acc._id });
  if (!r.deletedCount) throw new HttpError(404, 'Rutina no encontrada');
  bustRoutines(req.acc._id);
  res.json({ ok: true });
}));

/* Administración propia (ADMIN_TOKEN) */
app.get('/api/admin/accounts', requireAdmin, wrap(async (req, res) => {
  const [accs, brs, rts] = await Promise.all([col('accounts').find({}).toArray(), col('branches').find({}).toArray(), col('routines').find({}).toArray()]);
  const count = (list, id) => list.filter((x) => x.accountId === id).length;
  res.json({ accounts: accs.map((a) => ({ ...pubAccount(a), createdAt: a.createdAt, branches: count(brs, a._id), routines: count(rts, a._id),
    devices: [...devices.values()].filter((d) => d.accountId === a._id).length })) });
}));
app.get('/api/admin/devices', requireAdmin, (req, res) => res.json({ devices: [...devices.values()].map((d) => ({ ...toPublic(d), accountId: d.accountId })) }));
app.post('/api/admin/devices/:id/assign', requireAdmin, wrap(async (req, res) => { // para equipos viejos sin prefijo de cuenta
  const d = devices.get(req.params.id), accountId = String((req.body || {}).accountId || '');
  if (!d) throw new HttpError(404, 'Equipo no encontrado');
  if (!(await col('accounts').findOne({ _id: accountId }))) throw new HttpError(404, 'Cuenta no encontrada');
  Object.assign(d, { accountId, branchId: null, zoneId: null }); persist(d); res.json(toPublic(d));
}));
app.delete('/api/admin/accounts/:id', requireAdmin, wrap(async (req, res) => {
  const id = req.params.id;
  if (!(await col('accounts').findOne({ _id: id }))) throw new HttpError(404, 'Cuenta no encontrada');
  for (const d of devices.values()) if (d.accountId === id) release(d);
  await Promise.all([col('routines').deleteMany({ accountId: id }), col('branches').deleteMany({ accountId: id }), col('accounts').deleteOne({ _id: id })]);
  res.json({ ok: true });
}));

app.use((req, res) => res.status(404).json({ error: 'Ruta no encontrada' }));
// eslint-disable-next-line no-unused-vars
app.use((err, req, res, next) => {
  if (err instanceof HttpError) return res.status(err.status).json({ error: err.message });
  if (err.type === 'entity.parse.failed') return res.status(400).json({ error: 'JSON inválido' });
  if (err.type === 'entity.too.large') return res.status(413).json({ error: 'Contenido demasiado grande' });
  console.error('[error]', err);
  res.status(500).json({ error: 'Error interno del servidor' });
});

/* ---------- Planificador: cada minuto aplica las rutinas por sucursal/zona ---------- */
const WEEKDAYS = { Sun: 0, Mon: 1, Tue: 2, Wed: 3, Thu: 4, Fri: 5, Sat: 6 };
function localNow(date = new Date()) {
  const parts = new Intl.DateTimeFormat('en-US', { timeZone: APP_TIMEZONE, weekday: 'short', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).formatToParts(date);
  const get = (t) => parts.find((p) => p.type === t).value;
  return { day: WEEKDAYS[get('weekday')], hhmm: `${get('hour')}:${get('minute')}` };
}
async function evaluateSchedules(now = localNow()) {
  const prevDay = (now.day + 6) % 7, changes = [];
  const routines = await col('routines').find({ enabled: true }).toArray();
  for (const r of routines) {
    const overnight = r.onTime && r.offTime && r.offTime < r.onTime;
    const fire = (state) => {
      for (const d of devices.values()) {
        if (d.accountId !== r.accountId || d.branchId !== r.branchId || (r.zoneId && d.zoneId !== r.zoneId) || d.desiredState === state) continue;
        d.desiredState = state; d.cmdAt = new Date().toISOString(); persist(d); changes.push({ id: d.id, state });
      }
    };
    if (r.onTime === now.hhmm && r.days.includes(now.day)) fire('ON');
    if (r.offTime === now.hhmm && r.days.includes(overnight ? prevDay : now.day)) fire('OFF');
  }
  for (const c of changes) console.log(`[scheduler] ${now.hhmm} → ${c.id}: ${c.state}`);
  return changes;
}

async function main() {
  try { new Intl.DateTimeFormat('en-US', { timeZone: APP_TIMEZONE }); } catch { console.error(`APP_TIMEZONE inválida: "${APP_TIMEZONE}"`); process.exit(1); }
  const missing = ['MONGODB_URI', 'JWT_SECRET', 'ADMIN_TOKEN', 'DEVICE_KEY'].filter((k) => !process.env[k]);
  if (missing.length) { console.error(`Faltan variables de entorno: ${missing.join(', ')}`); process.exit(1); }
  try {
    await mongo.connect();
    for (const d of await col('devices').find({}).toArray()) {
      const dev = { ...newDevice(d._id, 'OFF'), ...d, id: d._id, pendingWifi: null };
      delete dev._id;
      if (wifiBusy(dev)) dev.wifiStatus = { ...dev.wifiStatus, state: 'cancelled', at: new Date().toISOString() }; // la clave pendiente no se guarda
      devices.set(dev.id, dev);
    }
    console.log(`[mongo] conectado: ${devices.size} equipo(s) cargado(s)`);
  } catch (err) { console.error('[mongo] No se pudo iniciar:', err.message); process.exit(1); }

  cron.schedule('* * * * *', () => evaluateSchedules().catch((e) => console.error('[scheduler]', e.message)), { timezone: APP_TIMEZONE });
  app.listen(PORT, () => console.log(`API lista en el puerto ${PORT} (zona horaria ${APP_TIMEZONE})`));
  process.on('SIGTERM', async () => { await flush(); await mongo.close(); process.exit(0); });
}

if (require.main === module) main();
module.exports = { app, devices, evaluateSchedules, localNow };
