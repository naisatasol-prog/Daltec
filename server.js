'use strict';

/**
 * ============================================================
 *  CONTROL DE AIRES v2 — BACKEND MULTI-CLIENTE (Express + MongoDB Atlas)
 * ============================================================
 *  - El ESP-01 NO cambia: sigue haciendo POST /api/devices/:id/status
 *    con la cabecera x-device-key y recibe { desired, pollSeconds, ... }.
 *  - Cada cliente crea su cuenta y recibe un ID de cuenta único (ej. K7M2QX9).
 *  - Un equipo pertenece a una cuenta si su DEVICE_ID empieza con "<ID-CUENTA>-".
 *    Ejemplo: K7M2QX9-oficina-1  (se pone al grabar el ESP, igual que hoy).
 *  - Jerarquía: cuenta → sucursales → zonas (pisos/áreas/naves, anidables) → equipos.
 *  - Rutinas por equipo, por zona (incluye subzonas) o por sucursal completa.
 *
 *  VARIABLES DE ENTORNO (Render → Environment):
 *    MONGODB_URI     cadena de conexión de Atlas (NUNCA en el código)
 *    JWT_SECRET      texto largo aleatorio para firmar sesiones
 *    DEVICE_KEY      clave de los ESP-01 (la misma que ya tienen grabada)
 *    ADMIN_EMAIL / ADMIN_PASSWORD   crean tu usuario administrador la primera vez
 *    APP_TIMEZONE, POLL_SECONDS, MONGODB_DB (opcionales)
 */

const express = require('express');
const cors = require('cors');
const cron = require('node-cron');
const crypto = require('crypto');
const jwt = require('jsonwebtoken');
const bcrypt = require('bcryptjs');
const { MongoClient } = require('mongodb');

const clamp = (n, min, max) => Math.min(max, Math.max(min, n));
const PORT = Number(process.env.PORT) || 3000;
const MONGODB_URI = process.env.MONGODB_URI;
const DB_NAME = process.env.MONGODB_DB || 'ac_control';
const JWT_SECRET = process.env.JWT_SECRET;
const DEVICE_KEY = process.env.DEVICE_KEY || '';
const DEFAULT_TZ = process.env.APP_TIMEZONE || 'America/Mexico_City';
const OPEN_SECONDS = clamp(Number(process.env.OPEN_SECONDS) || 5, 1, 30); // cuánto se mantiene energizado el relé al abrir
const POLL_SECONDS = clamp(Number(process.env.POLL_SECONDS) || 10, 3, 120);
const MAX_ROUTINES_PER_ACCOUNT = 200;
const MAX_ORPHANS = 500;

const ID_RE = /^[a-z0-9][a-z0-9_-]{0,39}$/i;
const TIME_RE = /^([01]\d|2[0-3]):[0-5]\d$/;
const EMAIL_RE = /^[^\s@]+@[^\s@]+\.[^\s@]{2,}$/;
const LOGO_RE = /^data:image\/(png|jpeg|webp|svg\+xml);base64,[A-Za-z0-9+/=]+$/;
const COLOR_RE = /^#[0-9a-f]{6}$/i;
const CODE_ALPHABET = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
const RESERVED_SLUGS = new Set(['admin', 'api', 'login', 'app', 'www']);

/* ------------------------------------------------------------
 *  Utilidades
 * ---------------------------------------------------------- */
class HttpError extends Error {
  constructor(status, message) {
    super(message);
    this.status = status;
  }
}
const ah = (fn) => (req, res, next) => Promise.resolve(fn(req, res, next)).catch(next);
const uid = () => crypto.randomUUID();
const text = (v, label, min, max) => {
  const s = String(v ?? '').trim();
  if (s.length < min || s.length > max) throw new HttpError(400, `${label}: entre ${min} y ${max} caracteres`);
  return s;
};
function safeEqual(a, b) {
  const A = Buffer.from(String(a));
  const B = Buffer.from(String(b));
  return A.length === B.length && crypto.timingSafeEqual(A, B);
}
function slugify(s) {
  return String(s)
    .normalize('NFD')
    .replace(/[\u0300-\u036f]/g, '')
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .slice(0, 40);
}
function genCode() {
  let s = '';
  for (const b of crypto.randomBytes(7)) s += CODE_ALPHABET[b % CODE_ALPHABET.length];
  return s;
}
function parseState(value) {
  const s = String(value || '').toUpperCase();
  if (s !== 'ON' && s !== 'OFF') throw new HttpError(400, 'El estado debe ser "ON" u "OFF"');
  return s;
}
function validTimezone(tz) {
  try {
    new Intl.DateTimeFormat('en-US', { timeZone: tz });
    return true;
  } catch {
    return false;
  }
}

// Limitador sencillo para login/registro (en memoria).
const attempts = new Map();
function rateLimit(key, max = 10, windowMs = 15 * 60 * 1000) {
  const now = Date.now();
  const arr = (attempts.get(key) || []).filter((t) => now - t < windowMs);
  if (arr.length >= max) throw new HttpError(429, 'Demasiados intentos. Espera unos minutos');
  arr.push(now);
  attempts.set(key, arr);
}
setInterval(() => attempts.clear(), 60 * 60 * 1000).unref();

/* ------------------------------------------------------------
 *  Base de datos y caché de equipos
 *  Los equipos viven en memoria (el ESP consulta cada pocos segundos) y se
 *  guardan en Mongo por lotes cuando algo cambia.
 * ---------------------------------------------------------- */
let cols = {};
const devices = new Map(); // deviceId(lowercase) -> doc
const LP_SECONDS = clamp(Number(process.env.LONGPOLL_SECONDS) || 20, 5, 50); // el equipo deja la consulta abierta; la orden llega al instante
const waiters = new Map(); // deviceId -> { res, timer }  (long-poll)
function wake(id) {
  const w = waiters.get(id);
  if (w && typeof w.release === 'function') w.release();
}
function wakeAccount(accountId) {
  if (!accountId) return;
  for (const d of devices.values()) {
    if (d.accountId === accountId) wake(d._id);
  }
}
const runtime = new Map(); // deviceId -> { pendingWifi, pendingOpen, lastSaved }
const accountCodes = new Set(); // códigos de cuenta en minúsculas
const dirty = new Set();

const rt = (id) => {
  if (!runtime.has(id)) runtime.set(id, { pendingWifi: null, pendingOpen: 0, lastSaved: 0 });
  return runtime.get(id);
};
const markDirty = (d) => dirty.add(d._id);

async function flushDirty() {
  if (!dirty.size || !cols.devices) return;
  const ids = [...dirty];
  dirty.clear();
  const ops = ids
    .map((id) => devices.get(id))
    .filter(Boolean)
    .map((d) => ({ replaceOne: { filter: { _id: d._id }, replacement: d, upsert: true } }));
  if (!ops.length) return;
  try {
    await cols.devices.bulkWrite(ops, { ordered: false });
  } catch (err) {
    console.error('[mongo] Error al guardar equipos:', err.message);
    ids.forEach((id) => dirty.add(id));
  }
}

/** Registro de accesos (aperturas desde el panel, botón de salida, cambios de estado). Nunca rompe la petición. */
function logEvent(d, type, who) {
  if (!d.accountId || !cols.events) return;
  cols.events
    .insertOne({ accountId: d.accountId, deviceId: d._id, name: d.name, type, who: who || null, at: new Date() })
    .catch((e) => console.error('[events]', e.message));
}

/** Desvincula el equipo de la cuenta (restablecer de fábrica): queda libre otra vez con su serie + código. */
function unlinkDevice(d, reported) {
  if (!d.accountId) return false;
  const aid = d.accountId;
  logEvent(d, 'reset', 'equipo');
  d.accountId = null;
  d.name = d._id;
  d.modelId = null;
  d.siteId = null;
  d.zoneId = null;
  d.projectId = null;
  d.sharedWith = [];
  d.wifiStatus = null;
  d.desiredState = reported || 'OFF';
  d.mode = d.desiredState === 'ON' ? 'open' : 'normal';
  rt(d._id).pendingWifi = null;
  rt(d._id).pendingOpen = 0;
  if (cols.routines) cols.routines.deleteMany({ accountId: aid, 'target.id': d._id }).catch((e) => console.error('[reset]', e.message));
  console.log(`[devices] ${d._id}: restablecido de fábrica → desvinculado de la cuenta ${aid}`);
  return true;
}

function newDevice(id, accountId, state) {
  return {
    _id: id,
    accountId: accountId || null,
    name: id,
    modelId: null,
    siteId: null,
    zoneId: null,
    projectId: null, // proyecto (agrupador) al que pertenece
    sharedWith: [], // cuentas con acceso compartido (control, no administración)
    desiredState: state || 'OFF',
    mode: state === 'ON' ? 'open' : 'normal', // normal | open (mantener abierta) | closed (mantener cerrada)
    vcHash: null, // hash del código de verificación (nunca se envía al navegador)
    reportedState: state || null,
    lastSeen: null,
    rssi: null,
    fw: null,
    ssid: null,
    wifiStatus: null,
    role: null,
    isMaster: false,
    masterId: null,
    slavesCount: 0,
    createdAt: new Date().toISOString(),
  };
}

/* ---------- Espera entre apagar y prender un apagador (evita ciclos rápidos que dañan el foco o el relé) ---------- */
const SWITCH_COOLDOWN_MS = clamp(Number(process.env.SWITCH_COOLDOWN_SECONDS) || 10, 0, 120) * 1000;
const isSwitchDevice = (d) => String(d.model || '').toUpperCase().includes('SW') || String(d.serial || d._id).toLowerCase().startsWith('dalsw');
const cooldownLeft = (d) => (isSwitchDevice(d) && d.lastToggleAt ? Math.max(0, Math.ceil((d.lastToggleAt + SWITCH_COOLDOWN_MS - Date.now()) / 1000)) : 0);

/* ---------- Modos de puerta (como un panel de acceso Hikvision) ----------
 *  normal = cerrada; el botón de salida funciona · open = mantener abierta · closed = mantener cerrada (botón bloqueado)
 *  "Abrir puerta" es un pulso aparte (no cambia el modo). */
const MODES = ['normal', 'open', 'closed'];
const modeOf = (d) => d.mode || (d.desiredState === 'ON' ? 'open' : 'normal');
function setMode(d, mode, who) {
  // (despierta al equipo si estaba esperando órdenes)
  if (!MODES.includes(mode)) throw new HttpError(400, 'Modo inválido (normal, open o closed)');
  if (modeOf(d) === mode) return false;
  d.mode = mode;
  d.desiredState = mode === 'open' ? 'ON' : 'OFF';
  if (isSwitchDevice(d)) d.lastToggleAt = Date.now(); // registra el momento del cambio para el cooldown
  logEvent(d, `mode-${mode}`, who);
  markDirty(d);
  wake(d._id);
  return true;
}
const vcHash = (id, code) => crypto.createHash('sha256').update(`${id}:${String(code).toUpperCase()}`).digest('hex');
const modeFromBody = (b) => b.mode || (b.state ? (parseState(b.state) === 'ON' ? 'open' : 'normal') : null);

function isOnline(d) {
  if (waiters.has(d._id)) return true;
  if (!d.lastSeen) return false;
  return Date.now() - Date.parse(d.lastSeen) < Math.max(30, POLL_SECONDS * 3) * 1000;
}

function toPublic(d) {
  const isSw = String(d.model || '').toUpperCase().includes('SW') || String(d.serial || d._id).toLowerCase().startsWith('dalsw');
  return {
    id: d._id,
    type: isSw ? 'switch' : 'door',
    accountId: d.accountId,
    name: d.name,
    modelId: d.modelId,
    siteId: d.siteId,
    zoneId: d.zoneId,
    projectId: d.projectId || null,
    sharedCount: (d.sharedWith || []).length,
    desiredState: d.desiredState,
    mode: modeOf(d),
    reportedState: d.reportedState,
    online: isOnline(d),
    lastSeen: d.lastSeen,
    rssi: d.rssi,
    fw: d.fw,
    ssid: d.ssid,
    serial: d.serial || d._id,
    model: d.model || null,
    openSecs: d.openSecs || null,
    lastCard: d.lastCard || null,
    lastCardAt: d.lastCardAt || null,
    cooldown: cooldownLeft(d), // segundos de espera restantes (apagadores)
    role: d.role || (d.isMaster ? 'master' : (isSw ? 'slave' : null)),
    isMaster: Boolean(d.isMaster),
    masterId: d.masterId || null,
    slavesCount: d.slavesCount || 0,
    wifiStatus: d.wifiStatus, // nunca incluye la contraseña
  };
}

/* ------------------------------------------------------------
 *  Cambio de Wi-Fi (misma lógica que la v1; la clave solo vive en memoria)
 * ---------------------------------------------------------- */
const wifiInProgress = (d) => Boolean(d.wifiStatus) && (d.wifiStatus.state === 'pending' || d.wifiStatus.state === 'sent');
function applyWifiResult(d, result) {
  if ((result !== 'ok' && result !== 'failed') || !wifiInProgress(d)) return false;
  d.wifiStatus = { ...d.wifiStatus, state: result, at: new Date().toISOString() };
  rt(d._id).pendingWifi = null;
  return true;
}

/* ------------------------------------------------------------
 *  Jerarquía y resolución de objetivos (equipo / zona / sucursal)
 * ---------------------------------------------------------- */
function zoneTree(rootId, zones) {
  const ids = new Set([rootId]);
  let grew = true;
  while (grew) {
    grew = false;
    for (const z of zones) {
      if (!ids.has(z._id) && ids.has(z.parentId)) {
        ids.add(z._id);
        grew = true;
      }
    }
  }
  return ids;
}

function devicesFor(accountId, target, zones) {
  const all = [...devices.values()].filter((d) => d.accountId === accountId);
  if (target.type === 'device') return all.filter((d) => d._id === target.id);
  if (target.type === 'site') return all.filter((d) => d.siteId === target.id);
  if (target.type === 'zone') {
    const ids = zoneTree(target.id, zones);
    return all.filter((d) => ids.has(d.zoneId));
  }
  return [];
}

async function checkTarget(accountId, target) {
  const t = target || {};
  if (!['device', 'zone', 'site'].includes(t.type) || typeof t.id !== 'string') throw new HttpError(400, 'Destino inválido');
  if (t.type === 'device') {
    const d = devices.get(t.id.toLowerCase());
    if (!d || d.accountId !== accountId) throw new HttpError(404, 'Equipo no encontrado');
    return { type: 'device', id: d._id };
  }
  const col = t.type === 'site' ? cols.sites : cols.zones;
  if (!(await col.findOne({ _id: t.id, accountId }))) throw new HttpError(404, t.type === 'site' ? 'Sucursal no encontrada' : 'Zona no encontrada');
  return { type: t.type, id: t.id };
}

/** Valida que sucursal y zona pertenezcan a la cuenta (y la zona a la sucursal). */
async function checkPlace(accountId, siteId, zoneId) {
  const out = { siteId: null, zoneId: null };
  if (siteId) {
    if (!(await cols.sites.findOne({ _id: String(siteId), accountId }))) throw new HttpError(400, 'La sucursal no existe');
    out.siteId = String(siteId);
  }
  if (zoneId) {
    if (!out.siteId) throw new HttpError(400, 'Elige primero la sucursal');
    if (!(await cols.zones.findOne({ _id: String(zoneId), accountId, siteId: out.siteId }))) throw new HttpError(400, 'La zona no pertenece a esa sucursal');
    out.zoneId = String(zoneId);
  }
  return out;
}

/* ------------------------------------------------------------
 *  Rutinas
 * ---------------------------------------------------------- */
function cleanTime(value, label) {
  if (value === null || value === undefined || value === '') return null;
  if (typeof value !== 'string' || !TIME_RE.test(value)) throw new HttpError(400, `${label}: la hora debe tener formato HH:MM (24 h)`);
  return value;
}
function cleanRoutine(item, label = 'Rutina') {
  const onTime = cleanTime(item.onTime, label);
  const offTime = cleanTime(item.offTime, label);
  if (!onTime && !offTime) throw new HttpError(400, `${label}: define al menos una hora (encendido o apagado)`);
  if (onTime && offTime && onTime === offTime) throw new HttpError(400, `${label}: encendido y apagado no pueden ser la misma hora`);
  const days = [...new Set((Array.isArray(item.days) ? item.days : []).map(Number))];
  if (!days.length || days.some((n) => !Number.isInteger(n) || n < 0 || n > 6)) throw new HttpError(400, `${label}: elige al menos un día`);
  days.sort((a, b) => a - b);
  return { name: String(item.name || '').trim().slice(0, 60), onTime, offTime, days, enabled: item.enabled !== false };
}

const WEEKDAYS = { Sun: 0, Mon: 1, Tue: 2, Wed: 3, Thu: 4, Fri: 5, Sat: 6 };
function localNow(tz, date = new Date()) {
  const parts = new Intl.DateTimeFormat('en-US', { timeZone: tz, weekday: 'short', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' }).formatToParts(date);
  const get = (type) => parts.find((p) => p.type === type).value;
  return { day: WEEKDAYS[get('weekday')], hhmm: `${get('hour')}:${get('minute')}` };
}

/** Se ejecuta cada minuto: aplica las rutinas de todas las cuentas activas, cada una en su zona horaria. */
async function evaluateSchedules(date = new Date()) {
  const routines = await cols.routines.find({ enabled: true }).toArray();
  if (!routines.length) return [];
  const accIds = [...new Set(routines.map((r) => r.accountId))];
  const accounts = new Map((await cols.accounts.find({ _id: { $in: accIds }, status: 'active' }).toArray()).map((a) => [a._id, a]));
  const zonesByAcc = new Map();
  for (const z of await cols.zones.find({ accountId: { $in: accIds } }).toArray()) {
    if (!zonesByAcc.has(z.accountId)) zonesByAcc.set(z.accountId, []);
    zonesByAcc.get(z.accountId).push(z);
  }

  const changes = [];
  for (const r of routines) {
    const acc = accounts.get(r.accountId);
    if (!acc) continue;
    const now = localNow(acc.timezone || DEFAULT_TZ, date);
    const prevDay = (now.day + 6) % 7;
    const overnight = r.onTime && r.offTime && r.offTime < r.onTime;
    let state = null;
    if (r.onTime === now.hhmm && r.days.includes(now.day)) state = 'ON';
    if (r.offTime === now.hhmm && r.days.includes(overnight ? prevDay : now.day)) state = 'OFF';
    if (!state) continue;
    for (const d of devicesFor(r.accountId, r.target, zonesByAcc.get(r.accountId) || [])) {
      const target = state === 'ON' ? 'open' : modeOf(d) === 'closed' ? 'closed' : 'normal'; // un plan no desbloquea "mantener cerrada"
      if (setMode(d, target, 'plan')) {
        changes.push({ id: d._id, state, routine: r._id });
        console.log(`[scheduler] ${now.hhmm} → ${d._id}: ${target}`);
      }
    }
  }
  return changes;
}

/* ------------------------------------------------------------
 *  App Express
 * ---------------------------------------------------------- */
const app = express();
app.disable('x-powered-by');
app.set('trust proxy', 1);
app.use(
  cors({
    origin: true, // cualquier página puede abrir el panel; la seguridad va en el token de inicio de sesión
    methods: ['GET', 'POST', 'PATCH', 'DELETE', 'OPTIONS'],
    allowedHeaders: ['Content-Type', 'Authorization', 'x-device-key'],
  })
);
app.use(express.json({ limit: '400kb' }));

app.get('/', (req, res) => res.json({ ok: true, service: 'acceso-control-api', version: '3.7.0' }));
app.get('/health', (req, res) => res.type('text').send('ok'));

/* ---------- Autenticación ---------- */
const sign = (user) => jwt.sign({ uid: user._id }, JWT_SECRET, { expiresIn: '7d' });
const bearer = (req) => {
  const h = req.get('authorization') || '';
  return h.startsWith('Bearer ') ? h.slice(7) : '';
};

const requireUser = ah(async (req, res, next) => {
  let payload;
  try {
    payload = jwt.verify(bearer(req), JWT_SECRET);
  } catch {
    throw new HttpError(401, 'Sesión expirada. Vuelve a entrar');
  }
  const user = await cols.users.findOne({ _id: payload.uid });
  if (!user) throw new HttpError(401, 'Sesión inválida');
  req.user = user;
  if (user.role !== 'admin') {
    const acc = await cols.accounts.findOne({ _id: user.accountId });
    if (!acc) throw new HttpError(401, 'Cuenta no encontrada');
    if (acc.status !== 'active') throw new HttpError(403, 'Tu cuenta está suspendida. Contacta al administrador');
    req.account = acc;
  }
  next();
});
const requireClient = [requireUser, (req, res, next) => (req.account ? next() : next(new HttpError(403, 'Solo para cuentas de cliente')))];
const requireAdmin = [requireUser, (req, res, next) => (req.user.role === 'admin' ? next() : next(new HttpError(403, 'Solo administradores')))];

function requireDeviceKey(req, res, next) {
  if (!DEVICE_KEY || !safeEqual(req.get('x-device-key') || '', DEVICE_KEY)) return next(new HttpError(401, 'Clave de dispositivo incorrecta'));
  next();
}

const publicAccount = (a) => ({
  id: a._id,
  name: a.name,
  slug: a.slug,
  timezone: a.timezone,
  status: a.status,
  branding: a.branding,
});

app.post(
  '/api/auth/register',
  ah(async (req, res) => {
    rateLimit(`reg:${req.ip}`, 10);
    const b = req.body || {};
    const email = String(b.email || '').trim().toLowerCase();
    if (!EMAIL_RE.test(email)) throw new HttpError(400, 'Correo inválido');
    const password = String(b.password || '');
    if (password.length < 8 || password.length > 100) throw new HttpError(400, 'La contraseña debe tener al menos 8 caracteres');
    const name = text(b.name, 'Nombre de la empresa', 2, 80);
    if (await cols.users.findOne({ email })) throw new HttpError(409, 'Ese correo ya tiene una cuenta');

    let slug = slugify(b.slug || name) || 'cliente';
    if (RESERVED_SLUGS.has(slug)) slug += '-1';
    for (let i = 2; await cols.accounts.findOne({ slug }); i++) slug = `${slugify(b.slug || name).slice(0, 36) || 'cliente'}-${i}`;

    let account;
    for (let tries = 0; tries < 8; tries++) {
      account = {
        _id: genCode(),
        name,
        slug,
        status: 'active',
        timezone: DEFAULT_TZ,
        branding: { color: '#d71920', logo: null },
        createdAt: new Date().toISOString(),
      };
      try {
        await cols.accounts.insertOne(account);
        break;
      } catch (err) {
        if (err.code !== 11000) throw err;
        account = null;
      }
    }
    if (!account) throw new HttpError(500, 'No se pudo generar un ID de cuenta. Intenta de nuevo');
    accountCodes.add(account._id.toLowerCase());

    const user = { _id: uid(), email, passHash: await bcrypt.hash(password, 11), role: 'owner', accountId: account._id, createdAt: new Date().toISOString() };
    await cols.users.insertOne(user);
    res.status(201).json({ token: sign(user), role: user.role, account: publicAccount(account) });
  })
);

app.post(
  '/api/auth/login',
  ah(async (req, res) => {
    const email = String((req.body || {}).email || '').trim().toLowerCase();
    rateLimit(`login:${req.ip}:${email}`, 10);
    const user = await cols.users.findOne({ email });
    const ok = user && (await bcrypt.compare(String((req.body || {}).password || ''), user.passHash));
    if (!ok) throw new HttpError(401, 'Correo o contraseña incorrectos');
    const account = user.accountId ? await cols.accounts.findOne({ _id: user.accountId }) : null;
    if (account && account.status !== 'active') throw new HttpError(403, 'Tu cuenta está suspendida. Contacta al administrador');
    res.json({ token: sign(user), role: user.role, account: account ? publicAccount(account) : null });
  })
);

app.post(
  '/api/auth/password',
  requireUser,
  ah(async (req, res) => {
    const { current, next } = req.body || {};
    if (!(await bcrypt.compare(String(current || ''), req.user.passHash))) throw new HttpError(400, 'La contraseña actual no es correcta');
    if (String(next || '').length < 8) throw new HttpError(400, 'La nueva contraseña debe tener al menos 8 caracteres');
    await cols.users.updateOne({ _id: req.user._id }, { $set: { passHash: await bcrypt.hash(String(next), 11) } });
    res.json({ ok: true });
  })
);

// Marca visible en la pantalla de acceso personalizada (?c=mi-empresa).
app.get(
  '/api/public/brand/:slug',
  ah(async (req, res) => {
    const a = await cols.accounts.findOne({ slug: String(req.params.slug).toLowerCase(), status: 'active' });
    if (!a) throw new HttpError(404, 'No existe esa empresa');
    res.json({ name: a.name, slug: a.slug, color: a.branding.color, logo: a.branding.logo });
  })
);

/* ---------- Cliente: vista general ---------- */
app.get(
  '/api/overview',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const [sites, zones, routines, models, people, projects] = await Promise.all([
      cols.sites.find({ accountId: aid }).sort({ name: 1 }).toArray(),
      cols.zones.find({ accountId: aid }).sort({ name: 1 }).toArray(),
      cols.routines.find({ accountId: aid }).toArray(),
      cols.models.find({ active: true }).sort({ brand: 1, name: 1 }).toArray(),
      cols.people ? cols.people.find({ accountId: aid }).sort({ name: 1 }).toArray() : [],
      cols.projects.find({ accountId: aid }).sort({ name: 1 }).toArray(),
    ]);
    const fix = (x) => ({ ...x, id: x._id });
    const events = req.query.events ? (await cols.events.find({ accountId: aid }).sort({ at: -1 }).limit(100).toArray()).map((e) => ({ id: String(e._id), deviceId: e.deviceId, name: e.name, type: e.type, who: e.who, at: e.at.toISOString() })) : undefined;
    res.json({
      events,
      serverTime: new Date().toISOString(),
      pollSeconds: POLL_SECONDS,
      account: publicAccount(req.account),
      email: req.user.email,
      sites: sites.map(fix),
      zones: zones.map(fix),
      routines: routines.map(fix),
      models: models.map(fix),
      people: people.map(fixPerson),
      devices: await overviewDevices(aid, projects),
      projects: await overviewProjects(aid, projects),
    });
  })
);

/* ------------------------------------------------------------
 *  PROYECTOS: agrupar equipos, compartir (control) o transferir (propiedad) por QR
 *  - projects: { _id, accountId, name, createdAt, remote? }
 *    remote = { ownerId, ownerName, ownerProjectId, deviceIds } → proyecto COMPARTIDO conmigo (solo control)
 *  - devices.projectId (proyecto propio) y devices.sharedWith (cuentas con acceso compartido)
 *  - shares: invitaciones de un solo uso, caducan en SHARE_MINUTES
 * ---------------------------------------------------------- */
const SHARE_MINUTES = 10;
const MAX_PROJECTS = 50;
const sharedWithMe = (d, aid) => d.accountId !== aid && Array.isArray(d.sharedWith) && d.sharedWith.includes(aid);

async function overviewDevices(aid, projects) {
  const remoteOf = new Map(); // deviceId -> { projectId, ownerName }
  for (const p of projects) if (p.remote) for (const id of p.remote.deviceIds || []) remoteOf.set(id, { projectId: p._id, ownerName: p.remote.ownerName });
  const out = [];
  for (const d of devices.values()) {
    if (d.accountId === aid) out.push(toPublic(d));
    else if (sharedWithMe(d, aid)) {
      const r = remoteOf.get(d._id);
      out.push({ ...toPublic(d), accountId: aid, shared: true, sharedBy: r ? r.ownerName : '', projectId: r ? r.projectId : null, siteId: null, zoneId: null, sharedCount: 0, wifiStatus: null, ssid: null, serial: null });
    }
  }
  return out.sort((a, b) => a.name.localeCompare(b.name));
}

async function overviewProjects(aid, projects) {
  const ownIds = new Set();
  const names = new Map();
  const sharedByProject = new Map(); // projectId -> Set(accountId)
  for (const d of devices.values()) {
    if (d.accountId !== aid || !d.projectId) continue;
    for (const a of d.sharedWith || []) {
      ownIds.add(a);
      if (!sharedByProject.has(d.projectId)) sharedByProject.set(d.projectId, new Set());
      sharedByProject.get(d.projectId).add(a);
    }
  }
  if (ownIds.size) for (const a of await cols.accounts.find({ _id: { $in: [...ownIds] } }, { projection: { name: 1 } }).toArray()) names.set(a._id, a.name);
  return projects.map((p) => ({
    id: p._id,
    name: p.name,
    createdAt: p.createdAt,
    shared: Boolean(p.remote),
    sharedBy: p.remote ? p.remote.ownerName : null,
    sharedWith: p.remote ? [] : [...(sharedByProject.get(p._id) || [])].map((id) => ({ id, name: names.get(id) || id })),
  }));
}

async function ownProject(aid, id) {
  const p = await cols.projects.findOne({ _id: String(id), accountId: aid });
  if (!p) throw new HttpError(404, 'No existe ese proyecto');
  return p;
}
const ownedProjectDevices = (aid, projectId) => [...devices.values()].filter((d) => d.accountId === aid && d.projectId === projectId);

app.post(
  '/api/projects',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const name = text((req.body || {}).name, 'Nombre del proyecto', 1, 60);
    if ((await cols.projects.countDocuments({ accountId: aid })) >= MAX_PROJECTS) throw new HttpError(400, 'Llegaste al máximo de proyectos');
    const p = { _id: uid(), accountId: aid, name, createdAt: new Date().toISOString() };
    await cols.projects.insertOne(p);
    res.status(201).json({ id: p._id, name: p.name, createdAt: p.createdAt, shared: false, sharedWith: [] });
  })
);

app.patch(
  '/api/projects/:id',
  requireClient,
  ah(async (req, res) => {
    const p = await ownProject(req.account._id, req.params.id);
    if (p.remote) throw new HttpError(403, 'Un proyecto compartido contigo no se puede renombrar');
    const name = text((req.body || {}).name, 'Nombre del proyecto', 1, 60);
    await cols.projects.updateOne({ _id: p._id }, { $set: { name } });
    res.json({ id: p._id, name });
  })
);

// Eliminar proyecto propio (los equipos quedan sin proyecto) o salir de un proyecto compartido conmigo.
app.delete(
  '/api/projects/:id',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const p = await ownProject(aid, req.params.id);
    if (p.remote) {
      for (const id of p.remote.deviceIds || []) {
        const d = devices.get(id);
        if (d && Array.isArray(d.sharedWith)) {
          d.sharedWith = d.sharedWith.filter((a) => a !== aid);
          markDirty(d);
        }
      }
    } else {
      for (const d of ownedProjectDevices(aid, p._id)) {
        d.projectId = null;
        markDirty(d);
      }
    }
    await cols.projects.deleteOne({ _id: p._id });
    res.json({ ok: true });
  })
);

// Mover equipos a un proyecto (projectId = null → sacarlos del proyecto).
app.post(
  '/api/projects/move',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const b = req.body || {};
    const ids = Array.isArray(b.deviceIds) ? b.deviceIds.map((x) => String(x).toLowerCase()).slice(0, 500) : [];
    if (!ids.length) throw new HttpError(400, 'Elige al menos un equipo');
    let projectId = null;
    if (b.projectId) {
      const p = await ownProject(aid, b.projectId);
      if (p.remote) throw new HttpError(400, 'No puedes mover equipos a un proyecto compartido contigo');
      projectId = p._id;
    }
    let moved = 0;
    for (const id of ids) {
      const d = devices.get(id);
      if (!d || d.accountId !== aid) continue;
      d.projectId = projectId;
      markDirty(d);
      moved++;
    }
    res.json({ moved });
  })
);

// Dejar de compartir (dueño): quita a una cuenta (o a todas) de los equipos del proyecto.
app.post(
  '/api/projects/:id/unshare',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const p = await ownProject(aid, req.params.id);
    const who = (req.body || {}).accountId ? String((req.body || {}).accountId) : null;
    let n = 0;
    for (const d of ownedProjectDevices(aid, p._id)) {
      if (!d.sharedWith || !d.sharedWith.length) continue;
      d.sharedWith = who ? d.sharedWith.filter((a) => a !== who) : [];
      markDirty(d);
      n++;
    }
    res.json({ ok: true, devices: n });
  })
);

/* ---------- Invitaciones por QR ---------- */
app.post(
  '/api/projects/:id/share',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    rateLimit(`share:${aid}`, 30, 60 * 60 * 1000);
    const p = await ownProject(aid, req.params.id);
    if (p.remote) throw new HttpError(403, 'Solo el dueño puede compartir o transferir este proyecto');
    const b = req.body || {};
    const mode = b.mode === 'transfer' ? 'transfer' : 'share';
    const wanted = new Set((Array.isArray(b.deviceIds) ? b.deviceIds : []).map((x) => String(x).toLowerCase()));
    const list = ownedProjectDevices(aid, p._id).filter((d) => wanted.has(d._id));
    if (!list.length) throw new HttpError(400, 'Elige al menos un dispositivo del proyecto');
    const token = crypto.randomBytes(12).toString('base64url');
    const now = Date.now();
    await cols.shares.insertOne({
      _id: token,
      accountId: aid,
      ownerName: req.account.name,
      projectId: p._id,
      projectName: p.name,
      deviceIds: list.map((d) => d._id),
      mode,
      used: false,
      createdAt: new Date(now),
      expiresAt: new Date(now + SHARE_MINUTES * 60 * 1000),
    });
    res.status(201).json({ token, mode, expiresAt: new Date(now + SHARE_MINUTES * 60 * 1000).toISOString(), devices: list.length });
  })
);

// Entregar sitio completo por QR
app.post(
  '/api/sites/:id/share',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    rateLimit(`sharesite:${aid}`, 30, 60 * 60 * 1000);
    const site = await cols.sites.findOne({ _id: String(req.params.id), accountId: aid });
    if (!site) throw new HttpError(404, 'Sucursal no encontrada');
    const zones = await cols.zones.find({ siteId: site._id, accountId: aid }).toArray();
    const list = [...devices.values()].filter((d) => d.accountId === aid && d.siteId === site._id);
    const token = crypto.randomBytes(12).toString('base64url');
    const now = Date.now();
    await cols.shares.insertOne({
      _id: token,
      accountId: aid,
      ownerName: req.account.name,
      type: 'site',
      siteId: site._id,
      siteName: site.name,
      siteKind: site.kind || 'sucursal',
      mode: 'transfer',
      deviceIds: list.map((d) => d._id),
      used: false,
      createdAt: new Date(now),
      expiresAt: new Date(now + SHARE_MINUTES * 60 * 1000),
    });
    res.status(201).json({ token, mode: 'transfer', type: 'site', expiresAt: new Date(now + SHARE_MINUTES * 60 * 1000).toISOString(), devices: list.length, zones: zones.length });
  })
);

async function loadShare(token, aid) {
  const sh = await cols.shares.findOne({ _id: String(token) });
  if (!sh || sh.used || sh.expiresAt.getTime() < Date.now()) throw new HttpError(404, 'Este QR ya caducó o ya fue usado. Pide uno nuevo');
  if (sh.accountId === aid) throw new HttpError(400, 'Este QR es de tu propia cuenta. Debe escanearlo otra cuenta');
  return sh;
}

app.get(
  '/api/share/:token',
  requireClient,
  ah(async (req, res) => {
    rateLimit(`sharelook:${req.account._id}`, 40, 15 * 60 * 1000);
    const sh = await loadShare(req.params.token, req.account._id);
    const list = sh.deviceIds.map((id) => devices.get(id)).filter((d) => d && d.accountId === sh.accountId);
    res.json({
      type: sh.type || 'project',
      mode: sh.mode,
      siteName: sh.siteName || null,
      projectName: sh.projectName || null,
      ownerName: sh.ownerName,
      expiresAt: sh.expiresAt.toISOString(),
      devices: list.map((d) => ({ id: d._id, name: d.name, type: isSwitchDevice(d) ? 'switch' : 'door' })),
    });
  })
);

app.post(
  '/api/share/:token/accept',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    rateLimit(`shareacc:${aid}`, 20, 15 * 60 * 1000);
    await loadShare(req.params.token, aid);
    // Se marca como usado de forma atómica: solo una cuenta puede aceptar.
    const got = await cols.shares.findOneAndUpdate({ _id: String(req.params.token), used: false, expiresAt: { $gt: new Date() } }, { $set: { used: true, usedBy: aid, usedAt: new Date() } });
    const sh = got && (got.value !== undefined ? got.value : got);
    if (!sh) throw new HttpError(404, 'Este QR ya caducó o ya fue usado. Pide uno nuevo');

    // Transferir sitio completo
    if (sh.type === 'site') {
      const site = await cols.sites.findOne({ _id: sh.siteId, accountId: sh.accountId });
      if (!site) throw new HttpError(409, 'Esa sucursal ya no está disponible');

      const ownerId = sh.accountId;
      // 1. Mover sucursal y sus zonas a la nueva cuenta
      await cols.sites.updateOne({ _id: site._id }, { $set: { accountId: aid } });
      await cols.zones.updateMany({ siteId: site._id, accountId: ownerId }, { $set: { accountId: aid } });

      // 2. Mover todos los dispositivos asignados a la sucursal
      const siteDevs = [...devices.values()].filter((d) => d.accountId === ownerId && d.siteId === site._id);
      for (const d of siteDevs) {
        logEvent(d, 'transfer-site', `${sh.ownerName} → ${req.account.name}`);
        d.accountId = aid;
        d.projectId = null;
        d.sharedWith = [];
        markDirty(d);
        wake(d._id);
      }

      // 3. Limpiar rutinas del dueño anterior para esta sucursal y sus dispositivos
      await cols.routines.deleteMany({ accountId: ownerId, 'target.id': { $in: [site._id, ...siteDevs.map((d) => d._id)] } });

      return res.json({ ok: true, type: 'site', mode: 'transfer', siteId: site._id, devices: siteDevs.length });
    }

    const list = sh.deviceIds.map((id) => devices.get(id)).filter((d) => d && d.accountId === sh.accountId);
    if (!list.length) throw new HttpError(409, 'Esos dispositivos ya no están disponibles');

    if (sh.mode === 'share') {
      let proj = await cols.projects.findOne({ accountId: aid, 'remote.ownerProjectId': sh.projectId });
      if (!proj) {
        proj = { _id: uid(), accountId: aid, name: sh.projectName, createdAt: new Date().toISOString(), remote: { ownerId: sh.accountId, ownerName: sh.ownerName, ownerProjectId: sh.projectId, deviceIds: [] } };
        await cols.projects.insertOne(proj);
      }
      const merged = [...new Set([...(proj.remote.deviceIds || []), ...list.map((d) => d._id)])];
      await cols.projects.updateOne({ _id: proj._id }, { $set: { 'remote.deviceIds': merged, 'remote.ownerName': sh.ownerName, name: sh.projectName } });
      for (const d of list) {
        d.sharedWith = [...new Set([...(d.sharedWith || []), aid])];
        markDirty(d);
        logEvent(d, 'share', `${sh.ownerName} → ${req.account.name}`);
      }
      return res.json({ ok: true, mode: 'share', projectId: proj._id, devices: list.length });
    }

    // Transferir proyecto: la propiedad pasa a esta cuenta. Se limpia ubicación, planes y accesos compartidos.
    const proj = { _id: uid(), accountId: aid, name: sh.projectName, createdAt: new Date().toISOString() };
    await cols.projects.insertOne(proj);
    const ownerId = sh.accountId;
    for (const d of list) {
      logEvent(d, 'transfer', `${sh.ownerName} → ${req.account.name}`);
      d.accountId = aid;
      d.projectId = proj._id;
      d.siteId = null;
      d.zoneId = null;
      d.sharedWith = [];
      markDirty(d);
      wake(d._id);
    }
    await cols.routines.deleteMany({ accountId: ownerId, 'target.id': { $in: list.map((d) => d._id) } });
    if (!ownedProjectDevices(ownerId, sh.projectId).length) await cols.projects.deleteOne({ _id: sh.projectId, accountId: ownerId });
    res.json({ ok: true, mode: 'transfer', projectId: proj._id, devices: list.length });
  })
);

/* ---------- Cliente: cuenta y marca ---------- */
app.patch(
  '/api/account',
  requireClient,
  ah(async (req, res) => {
    const b = req.body || {};
    const set = {};
    if (b.name !== undefined) set.name = text(b.name, 'Nombre', 2, 80);
    if (b.slug !== undefined) {
      const slug = slugify(b.slug);
      if (slug.length < 3 || RESERVED_SLUGS.has(slug)) throw new HttpError(400, 'El enlace debe tener al menos 3 letras/números y no ser reservado');
      if (await cols.accounts.findOne({ slug, _id: { $ne: req.account._id } })) throw new HttpError(409, 'Ese enlace ya está en uso');
      set.slug = slug;
    }
    if (b.timezone !== undefined) {
      if (!validTimezone(String(b.timezone))) throw new HttpError(400, 'Zona horaria inválida (ej. America/Mexico_City)');
      set.timezone = String(b.timezone);
    }
    if (b.color !== undefined) {
      if (!COLOR_RE.test(String(b.color))) throw new HttpError(400, 'Color inválido');
      set['branding.color'] = String(b.color);
    }
    if (b.logo !== undefined) {
      if (b.logo === null) set['branding.logo'] = null;
      else if (typeof b.logo === 'string' && b.logo.length <= 250000 && LOGO_RE.test(b.logo)) set['branding.logo'] = b.logo;
      else throw new HttpError(400, 'Logo inválido: usa PNG, JPG, WebP o SVG de máximo ~180 KB');
    }
    if (Object.keys(set).length) await cols.accounts.updateOne({ _id: req.account._id }, { $set: set });
    res.json(publicAccount(await cols.accounts.findOne({ _id: req.account._id })));
  })
);

/* ---------- Cliente: sucursales ---------- */
const SITE_KINDS = ['sucursal', 'parque', 'oficina', 'planta', 'otro'];
const ZONE_KINDS = ['piso', 'area', 'nave', 'bahia', 'edificio', 'sala', 'otro'];

app.post(
  '/api/sites',
  requireClient,
  ah(async (req, res) => {
    const b = req.body || {};
    if ((await cols.sites.countDocuments({ accountId: req.account._id })) >= 200) throw new HttpError(400, 'Límite de sucursales alcanzado');
    const site = {
      _id: uid(),
      accountId: req.account._id,
      name: text(b.name, 'Nombre', 1, 60),
      kind: SITE_KINDS.includes(b.kind) ? b.kind : 'sucursal',
      address: String(b.address || '').trim().slice(0, 160),
    };
    await cols.sites.insertOne(site);
    res.status(201).json({ ...site, id: site._id });
  })
);
app.patch(
  '/api/sites/:id',
  requireClient,
  ah(async (req, res) => {
    const b = req.body || {};
    const set = {};
    if (b.name !== undefined) set.name = text(b.name, 'Nombre', 1, 60);
    if (b.kind !== undefined && SITE_KINDS.includes(b.kind)) set.kind = b.kind;
    if (b.address !== undefined) set.address = String(b.address).trim().slice(0, 160);
    const r = await cols.sites.findOneAndUpdate({ _id: req.params.id, accountId: req.account._id }, { $set: set }, { returnDocument: 'after' });
    if (!r) throw new HttpError(404, 'Sucursal no encontrada');
    res.json({ ...r, id: r._id });
  })
);
app.delete(
  '/api/sites/:id',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    if (!(await cols.sites.findOne({ _id: req.params.id, accountId: aid }))) throw new HttpError(404, 'Sucursal no encontrada');
    const zones = await cols.zones.find({ siteId: req.params.id, accountId: aid }).toArray();
    const targetIds = [req.params.id, ...zones.map((z) => z._id)];
    for (const d of devices.values()) if (d.accountId === aid && d.siteId === req.params.id) Object.assign(d, { siteId: null, zoneId: null }) && markDirty(d);
    await Promise.all([
      cols.zones.deleteMany({ siteId: req.params.id, accountId: aid }),
      cols.routines.deleteMany({ accountId: aid, 'target.id': { $in: targetIds } }),
      cols.sites.deleteOne({ _id: req.params.id, accountId: aid }),
    ]);
    res.json({ ok: true });
  })
);

/* ---------- Cliente: zonas (pisos, áreas, naves, bahías…; anidables) ---------- */
app.post(
  '/api/zones',
  requireClient,
  ah(async (req, res) => {
    const b = req.body || {};
    const aid = req.account._id;
    const site = await cols.sites.findOne({ _id: String(b.siteId || ''), accountId: aid });
    if (!site) throw new HttpError(400, 'La sucursal no existe');
    let parentId = null;
    if (b.parentId) {
      if (!(await cols.zones.findOne({ _id: String(b.parentId), accountId: aid, siteId: site._id }))) throw new HttpError(400, 'La zona padre no existe en esa sucursal');
      parentId = String(b.parentId);
    }
    const zone = { _id: uid(), accountId: aid, siteId: site._id, parentId, name: text(b.name, 'Nombre', 1, 60), kind: ZONE_KINDS.includes(b.kind) ? b.kind : 'area' };
    await cols.zones.insertOne(zone);
    res.status(201).json({ ...zone, id: zone._id });
  })
);
app.patch(
  '/api/zones/:id',
  requireClient,
  ah(async (req, res) => {
    const b = req.body || {};
    const set = {};
    if (b.name !== undefined) set.name = text(b.name, 'Nombre', 1, 60);
    if (b.kind !== undefined && ZONE_KINDS.includes(b.kind)) set.kind = b.kind;
    const r = await cols.zones.findOneAndUpdate({ _id: req.params.id, accountId: req.account._id }, { $set: set }, { returnDocument: 'after' });
    if (!r) throw new HttpError(404, 'Zona no encontrada');
    res.json({ ...r, id: r._id });
  })
);
app.delete(
  '/api/zones/:id',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const zones = await cols.zones.find({ accountId: aid }).toArray();
    if (!zones.some((z) => z._id === req.params.id)) throw new HttpError(404, 'Zona no encontrada');
    const ids = zoneTree(req.params.id, zones);
    for (const d of devices.values()) if (d.accountId === aid && ids.has(d.zoneId)) d.zoneId = null, markDirty(d);
    await Promise.all([cols.zones.deleteMany({ accountId: aid, _id: { $in: [...ids] } }), cols.routines.deleteMany({ accountId: aid, 'target.id': { $in: [...ids] } })]);
    res.json({ ok: true });
  })
);

/* ---------- Cliente: equipos ---------- */
/* Agregar un dispositivo con número de serie + código de verificación (como Hik-Connect).
 * El equipo debe haberse conectado antes a internet (así el servidor conoce su código). */
app.post(
  '/api/devices',
  requireClient,
  ah(async (req, res) => {
    const b = req.body || {};
    const aid = req.account._id;
    rateLimit(`claim:${aid}`, 15);
    const id = String(b.serial || b.deviceId || '').trim().toLowerCase();
    const code = String(b.code || '').trim();
    if (!ID_RE.test(id)) throw new HttpError(400, 'Número de serie inválido (letras, números, - o _)');
    if (!/^[A-Za-z0-9]{4,12}$/.test(code)) throw new HttpError(400, 'Escribe el código de verificación de la etiqueta (4 a 12 letras o números)');
    const place = await checkPlace(aid, b.siteId, b.zoneId);
    if (b.modelId && !(await cols.models.findOne({ _id: String(b.modelId), active: true }))) throw new HttpError(400, 'Modelo no válido');

    const d = devices.get(id);
    if (!d) throw new HttpError(404, 'No encontramos ese equipo. Revisa el número de serie y que esté encendido y conectado a internet.');
    if (d.accountId === aid) throw new HttpError(409, 'Este dispositivo ya está en tu cuenta');
    if (d.accountId) throw new HttpError(409, 'Este dispositivo ya está agregado a otra cuenta');
    if (!d.vcHash || d.vcHash !== vcHash(id, code)) throw new HttpError(403, 'Código de verificación incorrecto');

    d.accountId = aid;
    d.name = String(b.name || '').trim().slice(0, 60) || id;
    d.modelId = b.modelId ? String(b.modelId) : null;
    Object.assign(d, place);
    markDirty(d);
    logEvent(d, 'added', req.user.email);
    res.status(201).json(toPublic(d));
  })
);

function ownDevice(req) {
  const d = devices.get(String(req.params.id).toLowerCase());
  if (!d || d.accountId !== req.account._id) throw new HttpError(404, 'No existe un equipo con ese ID');
  return d;
}
// Dueño o cuenta con acceso compartido (solo para controlar: abrir / cambiar modo).
function accessDevice(req) {
  const d = devices.get(String(req.params.id).toLowerCase());
  if (!d || (d.accountId !== req.account._id && !sharedWithMe(d, req.account._id))) throw new HttpError(404, 'No existe un equipo con ese ID');
  return d;
}

app.patch(
  '/api/devices/:id',
  requireClient,
  ah(async (req, res) => {
    const d = ownDevice(req);
    const b = req.body || {};
    if (b.name !== undefined) d.name = text(b.name, 'Nombre', 1, 60);
    if (b.modelId !== undefined) {
      if (b.modelId && !(await cols.models.findOne({ _id: String(b.modelId), active: true }))) throw new HttpError(400, 'Modelo no válido');
      d.modelId = b.modelId ? String(b.modelId) : null;
    }
    if (b.siteId !== undefined || b.zoneId !== undefined) Object.assign(d, await checkPlace(req.account._id, b.siteId, b.zoneId));
    if (b.projectId !== undefined) {
      if (b.projectId) {
        const p = await ownProject(req.account._id, b.projectId);
        if (p.remote) throw new HttpError(400, 'No puedes mover equipos a un proyecto compartido contigo');
        d.projectId = p._id;
      } else d.projectId = null;
    }
    markDirty(d);
    res.json(toPublic(d));
  })
);

app.post(
  '/api/devices/:id/command',
  requireClient,
  ah(async (req, res) => {
    const d = accessDevice(req);
    const next = modeFromBody(req.body || {});
    const left = next && next !== modeOf(d) ? cooldownLeft(d) : 0;
    if (left > 0) throw new HttpError(429, `Espera ${left} s antes de volver a cambiar el apagador`);
    setMode(d, next, req.user.email);
    res.json(toPublic(d));
  })
);

// Abrir ahora: el DALTEC energiza el relé OPEN_SECONDS y vuelve solo a su estado fijo (cerrada o abierta).
app.post(
  '/api/devices/:id/open',
  requireClient,
  ah(async (req, res) => {
    const d = accessDevice(req);
    if (isSwitchDevice(d)) throw new HttpError(400, 'Los apagadores no se abren: enciéndelos o apágalos');
    rt(d._id).pendingOpen = OPEN_SECONDS;
    wake(d._id);
    logEvent(d, 'open-panel', req.user.email);
    res.json({ ok: true, seconds: OPEN_SECONDS, device: toPublic(d) });
  })
);

app.post(
  '/api/open',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const target = await checkTarget(aid, (req.body || {}).target);
    const zones = await cols.zones.find({ accountId: aid }).toArray();
    const list = devicesFor(aid, target, zones).filter((d) => !isSwitchDevice(d)); // "abrir" solo aplica a puertas
    for (const d of list) {
      rt(d._id).pendingOpen = OPEN_SECONDS;
      wake(d._id);
      logEvent(d, 'open-panel', req.user.email);
    }
    res.json({ affected: list.length, seconds: OPEN_SECONDS });
  })
);

// Encender/apagar de golpe una zona (con subzonas) o una sucursal completa.
app.post(
  '/api/command',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const mode = modeFromBody(req.body || {});
    if (!MODES.includes(mode)) throw new HttpError(400, 'Modo inválido (normal, open o closed)');
    const target = await checkTarget(aid, (req.body || {}).target);
    const zones = await cols.zones.find({ accountId: aid }).toArray();
    const kind = (req.body || {}).kind; // 'door' | 'switch' (opcional): evita mezclar puertas con apagadores
    const list = devicesFor(aid, target, zones).filter((d) => !kind || (kind === 'switch') === isSwitchDevice(d));
    const ready = list.filter((d) => !(mode !== modeOf(d) && cooldownLeft(d) > 0)); // los apagadores en espera se omiten
    for (const d of ready) setMode(d, mode, req.user.email);
    res.json({ affected: ready.length, skipped: list.length - ready.length, mode });
  })
);

app.post(
  '/api/devices/:id/wifi',
  requireClient,
  ah(async (req, res) => {
    const d = ownDevice(req);
    const b = req.body || {};
    const ssid = typeof b.ssid === 'string' ? b.ssid : '';
    const password = typeof b.password === 'string' ? b.password : '';
    const sb = Buffer.byteLength(ssid, 'utf8');
    const pb = Buffer.byteLength(password, 'utf8');
    if (sb < 1 || sb > 32) throw new HttpError(400, 'El nombre de la red debe tener entre 1 y 32 caracteres');
    if (pb !== 0 && (pb < 8 || pb > 63)) throw new HttpError(400, 'La contraseña debe tener entre 8 y 63 caracteres (vacía solo si la red es abierta)');
    if (wifiInProgress(d)) throw new HttpError(409, 'Ya hay un cambio de red en curso. Espera el resultado o cancélalo');
    rt(d._id).pendingWifi = { ssid, password };
    d.wifiStatus = { state: 'pending', ssid, at: new Date().toISOString() };
    markDirty(d);
    wake(d._id);
    res.json(toPublic(d));
  })
);
app.delete(
  '/api/devices/:id/wifi',
  requireClient,
  ah(async (req, res) => {
    const d = ownDevice(req);
    if (!wifiInProgress(d)) throw new HttpError(409, 'No hay un cambio de red en curso');
    rt(d._id).pendingWifi = null;
    d.wifiStatus = { ...d.wifiStatus, state: 'cancelled', at: new Date().toISOString() };
    markDirty(d);
    res.json(toPublic(d));
  })
);

app.delete(
  '/api/devices/:id',
  requireClient,
  ah(async (req, res) => {
    const d = ownDevice(req);
    devices.delete(d._id);
    runtime.delete(d._id);
    dirty.delete(d._id);
    await Promise.all([cols.devices.deleteOne({ _id: d._id }), cols.routines.deleteMany({ accountId: d.accountId, 'target.id': d._id })]);
    res.json({ ok: true });
  })
);

/* ---------- Cliente: rutinas ---------- */
app.post(
  '/api/routines',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    if ((await cols.routines.countDocuments({ accountId: aid })) >= MAX_ROUTINES_PER_ACCOUNT) throw new HttpError(400, `Máximo ${MAX_ROUTINES_PER_ACCOUNT} rutinas`);
    const r = { _id: uid(), accountId: aid, target: await checkTarget(aid, (req.body || {}).target), ...cleanRoutine(req.body || {}) };
    await cols.routines.insertOne(r);
    res.status(201).json({ ...r, id: r._id });
  })
);
app.patch(
  '/api/routines/:id',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const cur = await cols.routines.findOne({ _id: req.params.id, accountId: aid });
    if (!cur) throw new HttpError(404, 'Rutina no encontrada');
    const b = { ...cur, ...(req.body || {}) };
    const set = cleanRoutine(b);
    if ((req.body || {}).target) set.target = await checkTarget(aid, req.body.target);
    await cols.routines.updateOne({ _id: cur._id }, { $set: set });
    res.json({ ...cur, ...set, id: cur._id });
  })
);
app.delete(
  '/api/routines/:id',
  requireClient,
  ah(async (req, res) => {
    const r = await cols.routines.deleteOne({ _id: req.params.id, accountId: req.account._id });
    if (!r.deletedCount) throw new HttpError(404, 'Rutina no encontrada');
    res.json({ ok: true });
  })
);

/* ---------- Cliente: personas y tarjetas de acceso ---------- */
const cleanCard = (c) => {
  if (typeof c !== 'string') return null;
  const s = c.trim().toUpperCase();
  return /^[0-9A-F]{8,20}$/.test(s) ? s : null;
};

const cleanPerson = (b) => {
  const name = String(b.name || '').trim().slice(0, 31);
  if (!name) throw new HttpError(400, 'El nombre es obligatorio');
  const no = String(b.no || '').trim().slice(0, 15);
  const enabled = b.enabled !== false;

  let cards = [];
  if (Array.isArray(b.cards)) {
    for (const c of b.cards) {
      const card = cleanCard(c);
      if (card && !cards.includes(card) && cards.length < 5) cards.push(card);
    }
  }

  let schedule = { enabled: false, days: [1, 2, 3, 4, 5], start: '08:00', end: '18:00' };
  if (b.schedule && typeof b.schedule === 'object') {
    const s = b.schedule;
    const schedEnabled = Boolean(s.enabled);
    let days = [1, 2, 3, 4, 5];
    if (Array.isArray(s.days)) {
      days = [...new Set(s.days.map(Number).filter((d) => d >= 0 && d <= 6))];
      if (!days.length) days = [1, 2, 3, 4, 5];
    }
    const TIME_RE = /^([01]\d|2[0-3]):[0-5]\d$/;
    const start = TIME_RE.test(s.start) ? s.start : '08:00';
    const end = TIME_RE.test(s.end) ? s.end : '18:00';
    schedule = { enabled: schedEnabled, days, start, end };
  }

  return { name, no, enabled, cards, schedule };
};

const cleanPersonUpdate = (b) => {
  const set = {};
  if (b.name !== undefined) {
    const name = String(b.name || '').trim().slice(0, 31);
    if (!name) throw new HttpError(400, 'El nombre es obligatorio');
    set.name = name;
  }
  if (b.no !== undefined) set.no = String(b.no || '').trim().slice(0, 15);
  if (b.enabled !== undefined) set.enabled = Boolean(b.enabled);
  if (Array.isArray(b.cards)) {
    const cards = [];
    for (const c of b.cards) {
      const card = cleanCard(c);
      if (card && !cards.includes(card) && cards.length < 5) cards.push(card);
    }
    set.cards = cards;
  }
  if (b.schedule && typeof b.schedule === 'object') {
    const s = b.schedule;
    const schedEnabled = Boolean(s.enabled);
    let days = [1, 2, 3, 4, 5];
    if (Array.isArray(s.days)) {
      days = [...new Set(s.days.map(Number).filter((d) => d >= 0 && d <= 6))];
      if (!days.length) days = [1, 2, 3, 4, 5];
    }
    const TIME_RE = /^([01]\d|2[0-3]):[0-5]\d$/;
    const start = TIME_RE.test(s.start) ? s.start : '08:00';
    const end = TIME_RE.test(s.end) ? s.end : '18:00';
    set.schedule = { enabled: schedEnabled, days, start, end };
  }
  return set;
};

const fixPerson = (p) => ({
  id: p._id,
  name: p.name,
  no: p.no || '',
  enabled: p.enabled !== false,
  cards: Array.isArray(p.cards) ? p.cards : [],
  schedule: p.schedule || { enabled: false, days: [1, 2, 3, 4, 5], start: '08:00', end: '18:00' },
  createdAt: p.createdAt,
  updatedAt: p.updatedAt,
});

async function bumpPeopleVer(accountId) {
  const ver = Math.floor(Date.now() / 1000);
  await cols.accounts.updateOne({ _id: accountId }, { $set: { peopleVer: ver } });
  wakeAccount(accountId);
  return ver;
}

app.get(
  '/api/people',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const list = await cols.people.find({ accountId: aid }).sort({ name: 1 }).toArray();
    res.json(list.map(fixPerson));
  })
);

app.post(
  '/api/people',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const count = await cols.people.countDocuments({ accountId: aid });
    if (count >= 100) throw new HttpError(400, 'Límite de 100 personas por cuenta alcanzado');
    const p = cleanPerson(req.body || {});
    if (p.cards && p.cards.length) {
      const dup = await cols.people.findOne({ accountId: aid, cards: { $in: p.cards } });
      if (dup) throw new HttpError(409, `Una de las tarjetas ya está asignada a ${dup.name}`);
    }
    p._id = uid();
    p.accountId = aid;
    p.createdAt = new Date().toISOString();
    p.updatedAt = p.createdAt;
    await cols.people.insertOne(p);
    await bumpPeopleVer(aid);
    res.status(201).json(fixPerson(p));
  })
);

app.patch(
  '/api/people/:id',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const cur = await cols.people.findOne({ _id: req.params.id, accountId: aid });
    if (!cur) throw new HttpError(404, 'Persona no encontrada');
    const update = cleanPersonUpdate(req.body || {});
    if (update.cards && update.cards.length) {
      const dup = await cols.people.findOne({ accountId: aid, _id: { $ne: cur._id }, cards: { $in: update.cards } });
      if (dup) throw new HttpError(409, `Una de las tarjetas ya está asignada a ${dup.name}`);
    }
    update.updatedAt = new Date().toISOString();
    await cols.people.updateOne({ _id: cur._id }, { $set: update });
    await bumpPeopleVer(aid);
    res.json(fixPerson({ ...cur, ...update }));
  })
);

app.delete(
  '/api/people/:id',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const r = await cols.people.deleteOne({ _id: req.params.id, accountId: aid });
    if (!r.deletedCount) throw new HttpError(404, 'Persona no encontrada');
    await bumpPeopleVer(aid);
    res.json({ ok: true });
  })
);

app.post(
  '/api/people/:id/cards',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const cur = await cols.people.findOne({ _id: req.params.id, accountId: aid });
    if (!cur) throw new HttpError(404, 'Persona no encontrada');
    const card = cleanCard((req.body || {}).card);
    if (!card) throw new HttpError(400, 'Código de tarjeta inválido (hexadecimal 8-20 dígitos)');
    if (cur.cards && cur.cards.includes(card)) throw new HttpError(409, 'Esta persona ya tiene registrada esa tarjeta');
    if (cur.cards && cur.cards.length >= 5) throw new HttpError(400, 'Máximo 5 tarjetas por persona');
    const dup = await cols.people.findOne({ accountId: aid, _id: { $ne: cur._id }, cards: card });
    if (dup) throw new HttpError(409, `La tarjeta ya está asignada a ${dup.name}`);
    await cols.people.updateOne({ _id: cur._id }, { $push: { cards: card }, $set: { updatedAt: new Date().toISOString() } });
    await bumpPeopleVer(aid);
    const updated = await cols.people.findOne({ _id: cur._id });
    res.json(fixPerson(updated));
  })
);

app.delete(
  '/api/people/:id/cards/:card',
  requireClient,
  ah(async (req, res) => {
    const aid = req.account._id;
    const cur = await cols.people.findOne({ _id: req.params.id, accountId: aid });
    if (!cur) throw new HttpError(404, 'Persona no encontrada');
    const card = cleanCard(req.params.card);
    if (!card) throw new HttpError(400, 'Tarjeta inválida');
    await cols.people.updateOne({ _id: cur._id }, { $pull: { cards: card }, $set: { updatedAt: new Date().toISOString() } });
    await bumpPeopleVer(aid);
    const updated = await cols.people.findOne({ _id: cur._id });
    res.json(fixPerson(updated));
  })
);

/* Endpoint para que el ESP32 descargue usuarios de su cuenta */
app.get(
  '/api/devices/:id/users',
  requireDeviceKey,
  ah(async (req, res) => {
    const id = String(req.params.id).toLowerCase();
    const d = devices.get(id);
    if (!d || !d.accountId) {
      return res.json({ version: 1, users: [] });
    }
    const acc = await cols.accounts.findOne({ _id: d.accountId });
    const people = await cols.people.find({ accountId: d.accountId }).sort({ name: 1 }).toArray();

    const users = people.map((p, idx) => {
      let daysMask = 0x7f;
      let sh = 0, sm = 0, eh = 23, em = 59;
      let hasSched = false;
      if (p.schedule && p.schedule.enabled) {
        hasSched = true;
        if (Array.isArray(p.schedule.days)) {
          daysMask = 0;
          for (const day of p.schedule.days) daysMask |= (1 << (Number(day) % 7));
        }
        if (typeof p.schedule.start === 'string') {
          const parts = p.schedule.start.split(':').map(Number);
          if (parts.length >= 2) { sh = parts[0] || 0; sm = parts[1] || 0; }
        }
        if (typeof p.schedule.end === 'string') {
          const parts = p.schedule.end.split(':').map(Number);
          if (parts.length >= 2) { eh = parts[0] || 0; em = parts[1] || 0; }
        }
      }
      return {
        id: idx + 1,
        name: String(p.name || '').slice(0, 31),
        no: String(p.no || '').slice(0, 15),
        en: p.enabled !== false,
        cards: Array.isArray(p.cards) ? p.cards.slice(0, 3) : [],
        hasSchedule: hasSched,
        days: daysMask,
        startHour: sh,
        startMin: sm,
        endHour: eh,
        endMin: em,
      };
    });

    res.json({
      version: (acc && acc.peopleVer) || 1,
      users,
    });
  })
);

/* ---------- ESP-01 (protocolo idéntico a la v1) ---------- */
app.post(
  '/api/devices/:id/status',
  requireDeviceKey,
  ah(async (req, res) => {
    const id = String(req.params.id).toLowerCase();
    if (!ID_RE.test(id)) throw new HttpError(400, 'ID inválido (usa letras, números, - o _; máx. 40)');
    const body = req.body || {};
    const reported = parseState(body.state);

    let d = devices.get(id);
    let changed = false;
    if (!d) {
      // Equipo nuevo: queda libre hasta que alguien lo agregue con su número de serie + código de verificación.
      const accountId = null;
      if (!accountId && [...devices.values()].filter((x) => !x.accountId).length >= MAX_ORPHANS) throw new HttpError(403, 'Demasiados equipos sin cuenta');
      d = newDevice(id, accountId, reported);
      devices.set(id, d);
      changed = true;
      console.log(`[devices] Equipo nuevo: ${id} → ${accountId || 'sin cuenta (lo asigna el administrador)'}`);
    }
    if (!d.lastSeen) {
      d.desiredState = reported; // primer contacto: se adopta el estado real para no cambiar la puerta por sorpresa
      d.mode = reported === 'ON' ? 'open' : 'normal';
      changed = true;
    }
    d.reportedState = reported;
    if (body.reset === true && unlinkDevice(d, reported)) changed = true;   // restablecido desde el propio equipo
    if (Number.isFinite(body.openSecs)) d.openSecs = Math.max(1, Math.min(30, Math.round(body.openSecs)));
    if (typeof body.serial === 'string' && ID_RE.test(body.serial)) d.serial = body.serial;
    if (typeof body.model === 'string') d.model = body.model.replace(/[^\w .-]/g, '').slice(0, 30);
    // Cambio hecho en el propio equipo (botón / contacto seco): el servidor lo adopta para no revertirlo.
    if (body.local === true && d.desiredState !== reported) {
      setMode(d, reported === 'ON' ? 'open' : 'normal', 'equipo');
      changed = true;
      console.log(`[devices] ${id}: cambio local → ${reported}`);
    }
    // Código de verificación (solo mientras el equipo no pertenece a ninguna cuenta).
    if (!d.accountId && typeof body.vc === 'string' && /^[A-Za-z0-9]{4,12}$/.test(body.vc)) {
      const h = vcHash(id, body.vc);
      if (d.vcHash !== h) { d.vcHash = h; changed = true; }
    }
    if (typeof body.lastCard === 'string' && /^([0-9A-Fa-f]{8,20})$/.test(body.lastCard)) {
      d.lastCard = body.lastCard.toUpperCase();
      d.lastCardAt = new Date().toISOString();
      changed = true;
    }
    if (typeof body.card === 'string' && /^([0-9A-Fa-f]{8,20})$/.test(body.card)) {
      d.lastCard = body.card.toUpperCase();
      d.lastCardAt = new Date().toISOString();
      changed = true;
    }
    if (body.evt === 'btn') logEvent(d, 'open-button'); // salida por botón / contacto seco
    if (body.evt === 'web') logEvent(d, 'open-web'); // apertura desde la interfaz web del propio equipo
    if (body.evt === 'card') logEvent(d, 'open-card', typeof body.who === 'string' ? body.who.replace(/[^\p{L}\p{N} ._-]/gu, '').slice(0, 40) : null); // apertura con tarjeta (ESP32 + PN532)
    if (body.evt === 'denied') logEvent(d, 'card-denied', typeof body.who === 'string' ? body.who.replace(/[^\p{L}\p{N} ._-]/gu, '').slice(0, 40) : null); // tarjeta rechazada
    if (body.evt === 'sched-denied') logEvent(d, 'card-sched', typeof body.who === 'string' ? body.who.replace(/[^\p{L}\p{N} ._-]/gu, '').slice(0, 40) : null); // fuera de horario permitido
    d.lastSeen = new Date().toISOString();
    if (Number.isFinite(body.rssi)) d.rssi = body.rssi;
    if (typeof body.fw === 'string') d.fw = body.fw.slice(0, 20);
    if (typeof body.isMaster === 'boolean') {
      if (d.isMaster !== body.isMaster) { d.isMaster = body.isMaster; changed = true; }
    }
    if (typeof body.role === 'string') {
      const r = body.role.slice(0, 20);
      if (d.role !== r) { d.role = r; changed = true; }
      if (typeof body.isMaster !== 'boolean') {
        const m = (r === 'master');
        if (d.isMaster !== m) { d.isMaster = m; changed = true; }
      }
    }
    if (typeof body.masterId === 'string') {
      const mid = body.masterId.slice(0, 40);
      if (d.masterId !== mid) { d.masterId = mid; changed = true; }
    }
    if (Number.isFinite(body.slavesCount)) {
      const sc = Math.max(0, Math.floor(body.slavesCount));
      if (d.slavesCount !== sc) { d.slavesCount = sc; changed = true; }
    }

    if (typeof body.ssidHex === 'string' && /^([0-9a-f]{2}){0,32}$/i.test(body.ssidHex)) {
      const ssid = Buffer.from(body.ssidHex, 'hex').toString('utf8');
      if (ssid !== d.ssid) {
        d.ssid = ssid;
        changed = true;
      }
    }
    if (applyWifiResult(d, body.wifiResult)) changed = true;

    // Verificar si el equipo necesita sincronizar la base de usuarios de su cuenta
    let needUsersSync = false;
    let currentPeopleVer = 1;
    if (d.accountId && cols.accounts) {
      const acc = await cols.accounts.findOne({ _id: d.accountId });
      currentPeopleVer = (acc && acc.peopleVer) || 1;
      const devUsersVer = Number(body.usersVer) || 0;
      if (devUsersVer !== currentPeopleVer) {
        needUsersSync = true;
      }
    }

    // Rutinas para ejecución local / offline en el propio equipo
    let devSched = [];
    let devTzOffset = -21600;
    if (d.accountId && cols.routines) {
      try {
        const acc = await cols.accounts.findOne({ _id: d.accountId });
        const tz = (acc && acc.timezone) || DEFAULT_TZ;
        const nowD = new Date();
        const dStr = nowD.toLocaleString('en-US', { timeZone: tz });
        const tzDate = new Date(dStr);
        devTzOffset = Math.round((tzDate.getTime() - nowD.getTime()) / 1000);

        const [zones, allRoutines] = await Promise.all([
          cols.zones.find({ accountId: d.accountId }).toArray(),
          cols.routines.find({ accountId: d.accountId, enabled: true }).toArray()
        ]);

        for (const r of allRoutines) {
          const devs = devicesFor(d.accountId, r.target, zones);
          if (devs.some((x) => x._id === d._id)) {
            let mask = 0;
            for (const day of (r.days || [])) mask |= (1 << day);
            const toMin = (t) => {
              if (!t) return -1;
              const [h, m] = t.split(':').map(Number);
              return h * 60 + m;
            };
            devSched.push({
              d: mask,
              on: toMin(r.onTime),
              off: toMin(r.offTime),
            });
          }
        }
      } catch (err) {
        console.error('[sched] Error calculando rutinas de equipo:', err.message);
      }
    }

    const r = rt(id);
    if (changed || Date.now() - r.lastSaved > 60000) {
      r.lastSaved = Date.now();
      markDirty(d);
    }

    // Respuesta: se arma al momento de enviarla (así, si el equipo esperaba, recibe lo último).
    const buildReply = () => {
      const reply = {
        desired: d.desiredState,
        lock: modeOf(d) === 'closed' ? 1 : 0,
        pollSeconds: POLL_SECONDS,
        lp: 1,
        serverTime: new Date().toISOString(),
        serverEpoch: Math.floor(Date.now() / 1000),
        tzOffset: devTzOffset,
        sched: devSched,
        usersVer: currentPeopleVer,
        usersSync: needUsersSync ? 1 : 0,
      };
      if (r.pendingOpen > 0) { reply.open = r.pendingOpen; r.pendingOpen = 0; }
      const pending = r.pendingWifi;
      if (pending) {
        reply.wifiSsidHex = Buffer.from(pending.ssid, 'utf8').toString('hex');
        reply.wifiPassHex = Buffer.from(pending.password, 'utf8').toString('hex');
        if (d.wifiStatus && d.wifiStatus.state === 'pending') {
          d.wifiStatus = { ...d.wifiStatus, state: 'sent', at: new Date().toISOString() };
          markDirty(d);
        }
      }
      return reply;
    };

    // ¿Hay algo que decirle ya? (orden de abrir, cambio de modo distinto de lo que reporta, red nueva por enviar, sincronización de usuarios)
    const urgent = Boolean(body.evt || body.local === true || body.reset === true || body.wifiResult) || r.pendingOpen > 0 || reported !== d.desiredState || (r.pendingWifi && d.wifiStatus && d.wifiStatus.state === 'pending') ||
      (modeOf(d) === 'closed') !== (body.lock === true) || needUsersSync;
    if (body.wait === 1 && !urgent) {
      // LONG-POLL: se deja la consulta abierta hasta LP_SECONDS; cualquier orden del panel la despierta al instante.
      const old = waiters.get(id);
      if (old) old.release();
      let done = false;
      const release = () => {
        if (done) return;
        done = true;
        clearTimeout(timer);
        if (waiters.get(id) === w) waiters.delete(id);
        d.lastSeen = new Date().toISOString();
        if (!res.writableEnded && !res.destroyed) res.json(buildReply());
      };
      const timer = setTimeout(release, LP_SECONDS * 1000);
      const w = { release };
      waiters.set(id, w);
      // OJO: se escucha 'close' de la RESPUESTA, no de la petición. En Node >= 16 el 'close' de req se dispara
      // en cuanto termina de leerse el cuerpo (a los pocos ms), lo que borraba el waiter y dejaba la consulta colgada.
      res.on('close', () => {
        if (done) return;
        done = true;
        clearTimeout(timer);
        if (waiters.get(id) === w) waiters.delete(id);
      });
      return;
    }
    res.json(buildReply());
  })
);

/* ---------- Administrador ---------- */
app.get(
  '/api/admin/accounts',
  requireAdmin,
  ah(async (req, res) => {
    const [accounts, users, siteCounts] = await Promise.all([
      cols.accounts.find({}).sort({ createdAt: -1 }).toArray(),
      cols.users.find({ role: 'owner' }).toArray(),
      cols.sites.aggregate([{ $group: { _id: '$accountId', n: { $sum: 1 } } }]).toArray(),
    ]);
    const sites = new Map(siteCounts.map((s) => [s._id, s.n]));
    res.json(
      accounts.map((a) => {
        const own = [...devices.values()].filter((d) => d.accountId === a._id);
        return {
          ...publicAccount(a),
          createdAt: a.createdAt,
          emails: users.filter((u) => u.accountId === a._id).map((u) => u.email),
          devices: own.length,
          online: own.filter(isOnline).length,
          sites: sites.get(a._id) || 0,
        };
      })
    );
  })
);
app.patch(
  '/api/admin/accounts/:id',
  requireAdmin,
  ah(async (req, res) => {
    const status = (req.body || {}).status;
    if (status !== 'active' && status !== 'suspended') throw new HttpError(400, 'Estado inválido');
    const r = await cols.accounts.updateOne({ _id: req.params.id }, { $set: { status } });
    if (!r.matchedCount) throw new HttpError(404, 'Cuenta no encontrada');
    res.json({ ok: true });
  })
);

app.get(
  '/api/admin/models',
  requireAdmin,
  ah(async (req, res) => res.json((await cols.models.find({}).sort({ brand: 1, name: 1 }).toArray()).map((m) => ({ ...m, id: m._id }))))
);
const cleanModel = (b) => ({
  brand: text(b.brand, 'Marca', 1, 40),
  name: text(b.name, 'Modelo', 1, 60),
  type: String(b.type || '').trim().slice(0, 30),
  notes: String(b.notes || '').trim().slice(0, 200),
  active: b.active !== false,
});
app.post(
  '/api/admin/models',
  requireAdmin,
  ah(async (req, res) => {
    const m = { _id: uid(), ...cleanModel(req.body || {}) };
    await cols.models.insertOne(m);
    res.status(201).json({ ...m, id: m._id });
  })
);
app.patch(
  '/api/admin/models/:id',
  requireAdmin,
  ah(async (req, res) => {
    const cur = await cols.models.findOne({ _id: req.params.id });
    if (!cur) throw new HttpError(404, 'Modelo no encontrado');
    const set = cleanModel({ ...cur, ...(req.body || {}) });
    await cols.models.updateOne({ _id: cur._id }, { $set: set });
    res.json({ ...cur, ...set, id: cur._id });
  })
);
app.delete(
  '/api/admin/models/:id',
  requireAdmin,
  ah(async (req, res) => {
    await cols.models.deleteOne({ _id: req.params.id });
    res.json({ ok: true });
  })
);

// Equipos que se conectaron sin pertenecer a ninguna cuenta (por ejemplo, los de la v1).
app.get('/api/admin/orphans', requireAdmin, (req, res) => res.json([...devices.values()].filter((d) => !d.accountId).map(toPublic)));
app.post(
  '/api/admin/devices/:id/assign',
  requireAdmin,
  ah(async (req, res) => {
    const d = devices.get(String(req.params.id).toLowerCase());
    if (!d) throw new HttpError(404, 'Equipo no encontrado');
    const accountId = String((req.body || {}).accountId || '').toUpperCase();
    if (!(await cols.accounts.findOne({ _id: accountId }))) throw new HttpError(404, 'Cuenta no encontrada');
    Object.assign(d, { accountId, siteId: null, zoneId: null });
    markDirty(d);
    res.json(toPublic(d));
  })
);

/* ============================================================
 *  INTEGRACIÓN CON ASISTENTES DE VOZ  —  Alexa & Google Home
 *  ──────────────────────────────────────────────────────────
 *  Flujo:
 *    1. El usuario abre la skill/acción en su app y hace "vincular cuenta".
 *    2. Se redirige a /oauth/authorize → pantalla de login de DALTEC.
 *    3. Tras iniciar sesión el servidor redirige con un code al asistente.
 *    4. El asistente canjea el code por access_token en /oauth/token.
 *    5. Las órdenes de voz llegan a /alexa/smart-home o /google/fulfillment.
 *
 *  Variables de entorno necesarias en Render:
 *    ALEXA_CLIENT_ID      (el que tú eliges, p.ej. "daltec-alexa")
 *    ALEXA_CLIENT_SECRET  (cadena larga aleatoria)
 *    GOOGLE_CLIENT_ID     (el que tú eliges, p.ej. "daltec-google")
 *    GOOGLE_CLIENT_SECRET (cadena larga aleatoria)
 *    APP_URL              (p.ej. https://daltec.onrender.com)
 * ============================================================ */

const ALEXA_CLIENT_ID     = process.env.ALEXA_CLIENT_ID     || 'daltec-alexa';
const ALEXA_CLIENT_SECRET = process.env.ALEXA_CLIENT_SECRET || '';
const GOOGLE_CLIENT_ID    = process.env.GOOGLE_CLIENT_ID    || 'daltec-google';
const GOOGLE_CLIENT_SECRET= process.env.GOOGLE_CLIENT_SECRET|| '';
const APP_URL = (process.env.APP_URL || 'https://daltec.onrender.com').replace(/\/$/, '');

// ── Tokens OAuth en memoria ──────────────────────────────────────────────────
// Map: token → { userId, accountId, expiresAt, isRefresh? }
const oauthTokens = new Map();
// Map: code  → { userId, accountId, clientId, redirectUri, expiresAt }
const oauthCodes  = new Map();
// Limpiar periódicamente tokens expirados
setInterval(() => {
  const now = Date.now();
  for (const [k, v] of oauthTokens) if (now > v.expiresAt) oauthTokens.delete(k);
  for (const [k, v] of oauthCodes)  if (now > v.expiresAt) oauthCodes.delete(k);
}, 5 * 60 * 1000).unref();

function genOauthToken() { return crypto.randomBytes(32).toString('hex'); }

function resolveOauthUser(token) {
  const data = oauthTokens.get(token);
  if (!data || Date.now() > data.expiresAt || data.isRefresh) return null;
  return data;
}

// ── Helpers HTML ─────────────────────────────────────────────────────────────
function esc(s) { return String(s || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/"/g,'&quot;'); }

// ── GET /oauth/authorize ─────────────────────────────────────────────────────
app.get('/oauth/authorize', (req, res) => {
  const { client_id, redirect_uri, state, response_type } = req.query;
  const validClients = new Set([ALEXA_CLIENT_ID, GOOGLE_CLIENT_ID].filter(Boolean));
  if (!validClients.has(client_id) || response_type !== 'code')
    return res.status(400).send('<h2>Parámetros OAuth inválidos</h2>');
  const platform = client_id === GOOGLE_CLIENT_ID ? 'Google Home' : 'Amazon Alexa';
  res.type('html').send(`<!DOCTYPE html>
<html lang="es">
<head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>DALTEC – Vincular cuenta</title>
<style>
  *{box-sizing:border-box;margin:0;padding:0}
  body{font-family:system-ui,sans-serif;background:#0d1117;color:#e6edf3;display:flex;align-items:center;justify-content:center;min-height:100vh;padding:1rem}
  .card{background:#161b22;border:1px solid #30363d;border-radius:12px;padding:2rem;width:100%;max-width:380px;text-align:center}
  h1{font-size:1.4rem;margin:.5rem 0 .3rem}
  p{color:#8b949e;font-size:.9rem;margin-bottom:1.5rem}
  label{display:block;text-align:left;font-size:.85rem;color:#8b949e;margin-bottom:.25rem}
  input{width:100%;padding:.6rem .8rem;border-radius:8px;border:1px solid #30363d;background:#0d1117;color:#e6edf3;font-size:1rem;margin-bottom:1rem;outline:none}
  input:focus{border-color:#d71920}
  .btn{width:100%;padding:.75rem;border-radius:8px;border:none;background:#d71920;color:#fff;font-size:1rem;font-weight:600;cursor:pointer}
  .btn:hover{background:#b01219}
  .err{color:#f85149;font-size:.85rem;margin-bottom:.75rem}
</style>
</head>
<body>
<div class="card">
  <div style="font-size:2.5rem">🔌</div>
  <h1>DALTEC</h1>
  <p>Inicia sesión para vincular tu cuenta con <strong>${esc(platform)}</strong></p>
  ${req.query.err ? `<p class="err">Correo o contraseña incorrectos</p>` : ''}
  <form method="POST" action="/oauth/authorize">
    <input type="hidden" name="client_id"    value="${esc(client_id)}">
    <input type="hidden" name="redirect_uri" value="${esc(redirect_uri)}">
    <input type="hidden" name="state"        value="${esc(state || '')}">
    <label>Correo electrónico</label>
    <input type="email"    name="email"    required autofocus placeholder="tu@correo.com">
    <label>Contraseña</label>
    <input type="password" name="password" required placeholder="••••••••">
    <button class="btn" type="submit">Autorizar acceso</button>
  </form>
</div>
</body></html>`);
});

// ── POST /oauth/authorize  (procesa el login y redirige con code) ─────────────
app.post('/oauth/authorize', express.urlencoded({ extended: false }), ah(async (req, res) => {
  const { client_id, redirect_uri, state, email, password } = req.body || {};
  const validClients = new Set([ALEXA_CLIENT_ID, GOOGLE_CLIENT_ID].filter(Boolean));
  if (!validClients.has(client_id)) return res.status(400).send('Cliente OAuth inválido');

  const user = cols.users && await cols.users.findOne({ email: String(email || '').trim().toLowerCase() });
  const ok   = user && (await bcrypt.compare(String(password || ''), user.passHash));
  if (!ok) {
    // Volver a la página de login con bandera de error
    const retryUrl = new URL(`${APP_URL}/oauth/authorize`);
    retryUrl.searchParams.set('response_type', 'code');
    retryUrl.searchParams.set('client_id', client_id);
    retryUrl.searchParams.set('redirect_uri', redirect_uri);
    if (state) retryUrl.searchParams.set('state', state);
    retryUrl.searchParams.set('err', '1');
    return res.redirect(retryUrl.toString());
  }

  const code = genOauthToken();
  oauthCodes.set(code, { userId: user._id, accountId: user.accountId, clientId: client_id, redirectUri: redirect_uri, expiresAt: Date.now() + 5 * 60 * 1000 });
  const dest = new URL(redirect_uri);
  dest.searchParams.set('code', code);
  if (state) dest.searchParams.set('state', state);
  res.redirect(dest.toString());
}));

// ── POST /oauth/token  (canjea code ó refresh_token por access_token) ─────────
app.post('/oauth/token', express.urlencoded({ extended: false }), ah(async (req, res) => {
  // Alexa puede mandar los params en query string o en el cuerpo urlencoded
  const b = Object.assign({}, req.query, req.body);
  const { grant_type, code, refresh_token, client_id, client_secret } = b;

  const validClient =
    (client_id === ALEXA_CLIENT_ID  && ALEXA_CLIENT_SECRET  && client_secret === ALEXA_CLIENT_SECRET) ||
    (client_id === GOOGLE_CLIENT_ID && GOOGLE_CLIENT_SECRET && client_secret === GOOGLE_CLIENT_SECRET);
  if (!validClient) return res.status(401).json({ error: 'invalid_client' });

  if (grant_type === 'authorization_code') {
    const data = oauthCodes.get(code);
    if (!data || Date.now() > data.expiresAt || data.clientId !== client_id)
      return res.status(400).json({ error: 'invalid_grant' });
    oauthCodes.delete(code);
    const access  = genOauthToken();
    const refresh = genOauthToken();
    oauthTokens.set(access,  { userId: data.userId, accountId: data.accountId, expiresAt: Date.now() + 3600 * 1000 });
    oauthTokens.set(refresh, { userId: data.userId, accountId: data.accountId, expiresAt: Date.now() + 30 * 24 * 3600 * 1000, isRefresh: true });
    return res.json({ access_token: access, token_type: 'Bearer', expires_in: 3600, refresh_token: refresh });
  }

  if (grant_type === 'refresh_token') {
    const data = oauthTokens.get(refresh_token);
    if (!data || !data.isRefresh || Date.now() > data.expiresAt)
      return res.status(400).json({ error: 'invalid_grant' });
    const access = genOauthToken();
    oauthTokens.set(access, { userId: data.userId, accountId: data.accountId, expiresAt: Date.now() + 3600 * 1000 });
    return res.json({ access_token: access, token_type: 'Bearer', expires_in: 3600, refresh_token });
  }

  res.status(400).json({ error: 'unsupported_grant_type' });
}));

// ── Alexa Smart Home Skill  POST /alexa/smart-home ────────────────────────────
app.post('/alexa/smart-home', ah(async (req, res) => {
  const event     = req.body || {};
  const directive = event.directive || {};
  const header    = directive.header || {};
  const ns        = header.namespace || '';
  const name      = header.name     || '';
  const corrToken = header.correlationToken;
  const token     = directive.endpoint?.scope?.token || directive.payload?.scope?.token || '';

  function alexaResp(respNs, respName, props, endpointId, extraPayload = {}) {
    return {
      event: {
        header: { namespace: respNs, name: respName, messageId: crypto.randomUUID(), correlationToken: corrToken, payloadVersion: '3' },
        endpoint: endpointId ? { endpointId, scope: { type: 'BearerToken', token } } : {},
        payload: extraPayload,
      },
      context: { properties: props || [] },
    };
  }
  function alexaErr(type, message) {
    return { event: { header: { namespace: 'Alexa', name: 'ErrorResponse', messageId: crypto.randomUUID(), correlationToken: corrToken, payloadVersion: '3' }, payload: { type, message } } };
  }
  function powerProp(state) {
    return [{ namespace: 'Alexa.PowerController', name: 'powerState', value: state, timeOfSample: new Date().toISOString(), uncertaintyInMilliseconds: 500 }];
  }

  // Discovery usa el token del scope del payload
  if (ns === 'Alexa.Discovery' && name === 'Discover') {
    const td = resolveOauthUser(token);
    if (!td) return res.json(alexaErr('INVALID_AUTHORIZATION_CREDENTIAL', 'Token inválido o expirado'));
    const endpoints = [...devices.values()]
      .filter(d => d.accountId === td.accountId)
      .map(d => ({
        endpointId: d._id,
        manufacturerName: 'DALTEC',
        friendlyName: d.name || d._id,
        description: isSwitchDevice(d) ? 'Apagador inteligente DALTEC' : 'Control de acceso DALTEC',
        displayCategories: isSwitchDevice(d) ? ['SWITCH', 'LIGHT'] : ['SMARTLOCK'],
        capabilities: [
          { type: 'AlexaInterface', interface: 'Alexa', version: '3' },
          { type: 'AlexaInterface', interface: 'Alexa.PowerController', version: '3',
            properties: { supported: [{ name: 'powerState' }], proactivelyReported: false, retrievable: true } },
          { type: 'AlexaInterface', interface: 'Alexa.EndpointHealth', version: '3',
            properties: { supported: [{ name: 'connectivity' }], proactivelyReported: false, retrievable: true } },
        ],
      }));
    return res.json({ event: { header: { namespace: 'Alexa.Discovery', name: 'Discover.Response', messageId: crypto.randomUUID(), payloadVersion: '3' }, payload: { endpoints } } });
  }

  // Resto de directivas: necesitan token válido y endpointId
  const td = resolveOauthUser(token);
  if (!td) return res.json(alexaErr('INVALID_AUTHORIZATION_CREDENTIAL', 'Token inválido o expirado'));

  const endpointId = (directive.endpoint?.endpointId || '').toLowerCase();
  const d = endpointId ? devices.get(endpointId) : null;
  if (!d || d.accountId !== td.accountId)
    return res.json(alexaErr('NO_SUCH_ENDPOINT', 'Equipo no encontrado en tu cuenta'));

  if (ns === 'Alexa.PowerController') {
    const targetMode = name === 'TurnOn' ? 'open' : 'normal';
    const cl = cooldownLeft(d);
    if (cl > 0 && targetMode !== modeOf(d))
      return res.json(alexaErr('THROTTLING_EXCEPTION', `Espera ${cl} segundos antes de volver a cambiar`));
    setMode(d, targetMode, 'alexa');
    return res.json(alexaResp('Alexa', 'Response', powerProp(d.desiredState), d._id));
  }

  if (ns === 'Alexa' && name === 'ReportState') {
    return res.json(alexaResp('Alexa', 'StateReport', [
      ...powerProp(d.desiredState),
      { namespace: 'Alexa.EndpointHealth', name: 'connectivity',
        value: { value: isOnline(d) ? 'OK' : 'UNREACHABLE' },
        timeOfSample: new Date().toISOString(), uncertaintyInMilliseconds: 500 },
    ], d._id));
  }

  res.json(alexaErr('INVALID_DIRECTIVE', `Directiva no soportada: ${ns}/${name}`));
}));

// ── Google Home Smart Home Action  POST /google/fulfillment ──────────────────
app.post('/google/fulfillment', ah(async (req, res) => {
  const h  = req.get('authorization') || '';
  const td = resolveOauthUser(h.startsWith('Bearer ') ? h.slice(7) : '');
  if (!td) return res.status(401).json({ requestId: (req.body || {}).requestId, payload: { errorCode: 'authFailure' } });

  const accountId = td.accountId;
  const inputs    = (req.body || {}).inputs || [];
  const requestId = (req.body || {}).requestId || crypto.randomUUID();

  const outputs = await Promise.all(inputs.map(async ({ intent, payload: p }) => {
    // ── SYNC ──────────────────────────────────────────────────────────────────
    if (intent === 'action.devices.SYNC') {
      return {
        agentUserId: accountId,
        devices: [...devices.values()].filter(d => d.accountId === accountId).map(d => ({
          id: d._id,
          type: isSwitchDevice(d) ? 'action.devices.types.SWITCH' : 'action.devices.types.OUTLET',
          traits: ['action.devices.traits.OnOff'],
          name: { name: d.name || d._id, defaultNames: [d._id], nicknames: [d.name || d._id] },
          willReportState: false,
          attributes: {},
          deviceInfo: { manufacturer: 'DALTEC', model: d.model || 'DAL-SW-1G', hwVersion: '1.0', swVersion: d.fw || '1.0' },
          roomHint: d.siteId || undefined,
        })),
      };
    }

    // ── QUERY ─────────────────────────────────────────────────────────────────
    if (intent === 'action.devices.QUERY') {
      const states = {};
      for (const { id } of (p?.devices || [])) {
        const d = devices.get(String(id).toLowerCase());
        if (!d || d.accountId !== accountId) { states[id] = { online: false, status: 'ERROR', errorCode: 'deviceNotFound' }; continue; }
        states[d._id] = { online: isOnline(d), on: d.desiredState === 'ON', status: 'SUCCESS' };
      }
      return { devices: states };
    }

    // ── EXECUTE ───────────────────────────────────────────────────────────────
    if (intent === 'action.devices.EXECUTE') {
      const commands = [];
      for (const cmd of (p?.commands || [])) {
        for (const execution of (cmd.execution || [])) {
          const successIds = [], failIds = [], offlineIds = [];
          for (const { id } of (cmd.devices || [])) {
            const d = devices.get(String(id).toLowerCase());
            if (!d || d.accountId !== accountId) { failIds.push(id); continue; }
            if (!isOnline(d)) { offlineIds.push(d._id); continue; }
            if (execution.command === 'action.devices.commands.OnOff') {
              const target = execution.params?.on ? 'open' : 'normal';
              if (cooldownLeft(d) > 0 && target !== modeOf(d)) { failIds.push(d._id); continue; }
              setMode(d, target, 'google');
              successIds.push(d._id);
            } else { failIds.push(d._id); }
          }
          if (successIds.length) commands.push({ ids: successIds, status: 'SUCCESS', states: { on: execution.params?.on } });
          if (offlineIds.length) commands.push({ ids: offlineIds, status: 'OFFLINE' });
          if (failIds.length)   commands.push({ ids: failIds,    status: 'ERROR', errorCode: 'commandInsertionError' });
        }
      }
      return { commands };
    }

    // ── DISCONNECT ────────────────────────────────────────────────────────────
    if (intent === 'action.devices.DISCONNECT') {
      for (const [t, v] of oauthTokens) if (v.accountId === accountId) oauthTokens.delete(t);
      return {};
    }

    return { errorCode: 'notSupported' };
  }));

  // Google espera el payload del primer intent directamente cuando hay un solo input
  res.json({ requestId, payload: outputs.length === 1 ? outputs[0] : outputs });
}));

app.use((req, res) => res.status(404).json({ error: 'Ruta no encontrada' }));
// eslint-disable-next-line no-unused-vars
app.use((err, req, res, next) => {
  if (err instanceof HttpError) return res.status(err.status).json({ error: err.message });
  if (err.type === 'entity.parse.failed') return res.status(400).json({ error: 'JSON inválido' });
  if (err.type === 'entity.too.large') return res.status(413).json({ error: 'Archivo demasiado grande' });
  console.error('[error]', err);
  res.status(500).json({ error: 'Error interno del servidor' });
});

/* ------------------------------------------------------------
 *  Arranque
 * ---------------------------------------------------------- */
async function main() {
  if (!MONGODB_URI) {
    console.error('Falta la variable de entorno MONGODB_URI (cadena de conexión de MongoDB Atlas).');
    process.exit(1);
  }
  if (!JWT_SECRET || JWT_SECRET.length < 24) {
    console.error('Falta JWT_SECRET (mínimo 24 caracteres aleatorios).');
    process.exit(1);
  }
  if (!DEVICE_KEY) console.warn('⚠️  DEVICE_KEY no definida: los ESP-01 serán rechazados.');
  if (!validTimezone(DEFAULT_TZ)) {
    console.error(`APP_TIMEZONE inválida: "${DEFAULT_TZ}"`);
    process.exit(1);
  }

  const client = new MongoClient(MONGODB_URI, { serverSelectionTimeoutMS: 15000 });
  await client.connect();
  const db = client.db(DB_NAME);
  cols = {
    accounts: db.collection('accounts'),
    users: db.collection('users'),
    sites: db.collection('sites'),
    zones: db.collection('zones'),
    devices: db.collection('devices'),
    routines: db.collection('routines'),
    models: db.collection('models'),
    events: db.collection('events'),
    people: db.collection('people'),
    projects: db.collection('projects'),
    shares: db.collection('shares'),
  };
  await Promise.all([
    cols.accounts.createIndex({ slug: 1 }, { unique: true }),
    cols.users.createIndex({ email: 1 }, { unique: true }),
    cols.sites.createIndex({ accountId: 1 }),
    cols.zones.createIndex({ accountId: 1, siteId: 1 }),
    cols.devices.createIndex({ accountId: 1 }),
    cols.routines.createIndex({ accountId: 1 }),
    cols.events.createIndex({ accountId: 1, at: -1 }),
    cols.events.createIndex({ at: 1 }, { expireAfterSeconds: 60 * 60 * 24 * 180 }), // el registro se conserva 180 días
    cols.people.createIndex({ accountId: 1 }),
    cols.people.createIndex({ accountId: 1, 'cards': 1 }),
    cols.projects.createIndex({ accountId: 1 }),
    cols.shares.createIndex({ expiresAt: 1 }, { expireAfterSeconds: 3600 }), // las invitaciones caducadas se limpian solas
  ]);

  // Administrador inicial (solo si no existe ninguno).
  if (process.env.ADMIN_EMAIL && process.env.ADMIN_PASSWORD && !(await cols.users.findOne({ role: 'admin' }))) {
    await cols.users.insertOne({
      _id: uid(),
      email: process.env.ADMIN_EMAIL.trim().toLowerCase(),
      passHash: await bcrypt.hash(process.env.ADMIN_PASSWORD, 11),
      role: 'admin',
      accountId: null,
      createdAt: new Date().toISOString(),
    });
    console.log('[admin] Usuario administrador creado');
  }
  // Modelos de ejemplo la primera vez.
  if (!(await cols.models.countDocuments())) {
    await cols.models.insertMany([
      { _id: uid(), brand: 'Genérico', name: 'Minisplit con control por termostato 24 V', type: 'minisplit', notes: '', active: true },
      { _id: uid(), brand: 'Genérico', name: 'Paquete / manejadora 24 V', type: 'paquete', notes: '', active: true },
    ]);
  }

  for (const a of await cols.accounts.find({}, { projection: { _id: 1 } }).toArray()) accountCodes.add(a._id.toLowerCase());
  for (const d of await cols.devices.find({}).toArray()) {
    d.wifiStatus = d.wifiStatus && (d.wifiStatus.state === 'pending' || d.wifiStatus.state === 'sent') ? { ...d.wifiStatus, state: 'cancelled', at: new Date().toISOString() } : d.wifiStatus;
    devices.set(d._id, d);
  }
  console.log(`[mongo] Conectado: ${accountCodes.size} cuenta(s), ${devices.size} equipo(s)`);

  setInterval(flushDirty, 2000).unref();
  cron.schedule('* * * * *', () => evaluateSchedules().catch((e) => console.error('[scheduler]', e.message)), { timezone: DEFAULT_TZ });

  const httpServer = app.listen(PORT, () => console.log(`API lista en el puerto ${PORT}`));
  // Las consultas largas del equipo (hasta LONGPOLL_SECONDS) no deben cortarse por los límites por defecto de Node.
  httpServer.requestTimeout = 0;
  httpServer.headersTimeout = 65000;
  httpServer.keepAliveTimeout = 65000;

  process.on('SIGTERM', async () => {
    await flushDirty();
    process.exit(0);
  });
}

if (require.main === module) {
  main().catch((err) => {
    console.error('Error al iniciar:', err.message);
    process.exit(1);
  });
}

module.exports = { app, evaluateSchedules, localNow, cleanRoutine, zoneTree };
