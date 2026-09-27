"use strict";

/*
  LinkUp
  Server: DnsServer.js

  Built-in Node.js modules only.
  No npm packages required.

  Main website:
    GotACrush.html

  Database:
    DigitalPandaDataBase.json

  HTTP:
    0.0.0.0:8080

  DNS:
    0.0.0.0:53

  IMPORTANT:
  - Random matching is text-only.
  - Users are matched only inside their exact age group.
  - Under-8 users cannot create accounts.
  - Age 19 is intentionally unavailable because the requested
    groups were 8-11, 12-13, 14-18 and 20-26.
*/

const http = require("http");
const net = require("net");
const dgram = require("dgram");
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");
const os = require("os");

const SERVER_NAME = "LinkUp";
const SERVER_FILE = "DnsServer.js";

const IS_RENDER = process.env.RENDER === "true" || !!process.env.RENDER_SERVICE_ID;
const SERVER_IP = process.env.SERVER_IP || "0.0.0.0";
// Render supplies PORT and terminates HTTPS in front of this process.
const HTTP_PORT = Number(process.env.PORT || 8080);
const DNS_PORT = Number(process.env.DNS_PORT || 53);
const ENABLE_DNS = process.env.ENABLE_DNS === "true" && !IS_RENDER;
const ENABLE_LBP3_TCP = process.env.ENABLE_LBP3_TCP === "true" && !IS_RENDER;
const ENABLE_LBP3_SERVICE = process.env.ENABLE_LBP3_SERVICE === "true" && !IS_RENDER;

/* ------------------------------------------------------------------ */
/* POWER 2 - LittleBigPlanet 3                                        */
/*                                                                       */
/* This subsystem is intentionally separate from POWER 1.              */
/* It owns its own state, security records, logs, listeners and        */
/* retry/health system. POWER 1 never calls into these functions.       */
/*                                                                       */
/* 443 is a raw TCP diagnostic/transport listener. It does not          */
/* impersonate Sony or terminate TLS with a forged certificate.         */
/* 8443 is the local LBP3 service API used for testing/implementation.  */
/* ------------------------------------------------------------------ */
const LBP3_TCP_PORT = 443;
const LBP3_SERVICE_PORT = 8443;
const LBP3_REQUEST_MAX_AGE_MS = 30 * 1000;
const LBP3_NONCE_TTL_MS = 2 * 60 * 1000;
const LBP3_RATE_WINDOW_MS = 10 * 1000;
const LBP3_RATE_MAX = 60;
const LBP3_RETRY_BASE_MS = 1000;
const LBP3_RETRY_MAX_MS = 30 * 1000;
const LBP3_MAX_PACKET_LOG_BYTES = 64;

const lbp3Power = {
  name: "POWER 2 - LittleBigPlanet 3",
  ip: SERVER_IP,
  tcpPort: LBP3_TCP_PORT,
  servicePort: LBP3_SERVICE_PORT,
  online: false,
  serviceOnline: false,
  requestCount: 0,
  successCount: 0,
  declinedCount: 0,
  failureCount: 0,
  blockedCount: 0,
  retryCount: 0,
  security: {
    usedNonces: new Map(),
    rate: new Map()
  },
  retry: {
    tcpAttempt: 0,
    serviceAttempt: 0,
    tcpTimer: null,
    serviceTimer: null
  },
  tcpServer: null,
  serviceServer: null
};

const DATA_DIR = process.env.DATA_DIR || __dirname;
const COOKIE_SECURE = IS_RENDER ? "; Secure" : "";
const HTML_FILE = path.join(__dirname, "GotACrush.html");
const DB_FILE = path.join(DATA_DIR, "DigitalPandaDataBase.json");

const ADMIN_OWNER = "DigitalPanda";

const SESSION_DAYS = 30;
const SESSION_MS = SESSION_DAYS * 24 * 60 * 60 * 1000;

const PRESENCE_TIMEOUT_MS = 2 * 60 * 1000;
const BODY_LIMIT = 15 * 1024 * 1024;

const MAX_EVENT_LOGS = 1000;
const MAX_DNS_LOGS = 5000;
const MAX_ACTION_LOGS = 300;

const RANDOM_MATCH_TIMEOUT_MS = 5 * 60 * 1000;
const RANDOM_MESSAGE_LIMIT = 200;
const DELETED_ACCOUNT_DELAY_MS = 18 * 1000;

const DNS_RATE_WINDOW_MS = 10 * 1000;
const DNS_RATE_MAX = 120;

const DNS_UPSTREAMS = [
  "1.1.1.1",
  "8.8.8.8",
  "9.9.9.9",
  "1.0.0.1"
];

const SUPPORTED_CONSOLES = [
  "Nintendo Switch",
  "Nintendo Switch 2",
  "Nintendo Wii U",
  "Nintendo Wii",
  "PlayStation 4",
  "PlayStation 5"
];

/*
  Exact age groups.

  The original requested ranges had 14 in both 12-14 and 14-18.
  That creates an overlap, so this server uses:
    8-11
    12-13
    14-18
    20-26

  Age 19 is unavailable.
*/
const AGE_GROUPS = [
  { id: "8-11", min: 8, max: 11 },
  { id: "12-13", min: 12, max: 13 },
  { id: "14-18", min: 14, max: 18 },
  { id: "20-26", min: 20, max: 26 }
];

const PERMANENT_ALLOWED_DOMAINS = [
  "roblox.com",
  "google.com",
  "youtube.com",
  "youtu.be",
  "x.com",
  "twitter.com",
  "chatgpt.com",
  "openai.com",
  "grok.com",
  "x.ai",
  "epicgames.com",
  "fortnite.com",
  "unrealengine.com"
];

const HARD_BANNED_DOMAINS = [
  "pornhub.com",
  "xvideos.com",
  "xnxx.com",
  "redtube.com",
  "youporn.com",
  "onlyfans.com",
  "bet365.com",
  "stake.com",
  "draftkings.com"
];

const BANNED_KEYWORDS = [
  "porn",
  "pornography",
  "xxx",
  "sexcam",
  "adultvideo",
  "gambling",
  "casino",
  "betting",
  "escort"
];

/* ------------------------------------------------------------------ */
/* State                                                               */
/* ------------------------------------------------------------------ */

let db = loadDatabase();

const dnsRate = new Map();
const dnsLogs = [];
const eventLogs = [];
const actionLogs = [];

const activeRandomQueue = new Map();
/*
  ageGroup -> userId
*/

const randomChats = new Map();
/*
  chatId -> {
    id,
    userA,
    userB,
    createdAt,
    updatedAt,
    messages: [],
    deletedUserId: null,
    deleteDeadline: null
  }
*/

const activeChatByUser = new Map();
/*
  userId -> randomChatId
*/

const deletedAccountTimers = new Map();

/* ------------------------------------------------------------------ */
/* Logging                                                             */
/* ------------------------------------------------------------------ */

function now() {
  return Date.now();
}

function iso(time = Date.now()) {
  return new Date(time).toISOString();
}

function pushLimited(array, item, max) {
  array.push(item);

  if (array.length > max) {
    array.splice(0, array.length - max);
  }
}

function logEvent(type, message, extra = {}) {
  const entry = {
    time: iso(),
    type,
    message,
    ...extra
  };

  pushLimited(eventLogs, entry, MAX_EVENT_LOGS);

  console.log(`[${entry.time}] [${type}] ${message}`);
}

function logAction(type, message, extra = {}) {
  const entry = {
    time: iso(),
    type,
    message,
    ...extra
  };

  pushLimited(actionLogs, entry, MAX_ACTION_LOGS);

  console.log(`[${entry.time}] [ACTION] ${message}`);
}

function logDns(message, extra = {}) {
  const entry = {
    time: iso(),
    message,
    ...extra
  };

  pushLimited(dnsLogs, entry, MAX_DNS_LOGS);
}

/* ------------------------------------------------------------------ */
/* Database                                                            */
/* ------------------------------------------------------------------ */

function defaultDatabase() {
  return {
    version: 4,

    server: SERVER_NAME,

    users: [],

    sessions: [],

    presence: [],

    posts: [],
    comments: [],
    games: [],

    messages: [],

    chatRequests: [],

    blockedUsers: [],

    reports: [],

    dnsUsage: {},
    dnsStats: {
      totalQueries: 0,
      blockedQueries: 0,
      forwardedQueries: 0
    },

    bannedIps: [],
    bannedDomains: [],
    allowedDomainsExtra: [],

    settings: {
      createdAt: iso(),
      updatedAt: iso()
    }
  };
}

function loadDatabase() {
  try {
    if (!fs.existsSync(DB_FILE)) {
      const fresh = defaultDatabase();
      saveDatabase(fresh);
      return fresh;
    }

    const raw = fs.readFileSync(DB_FILE, "utf8");
    const parsed = JSON.parse(raw);

    const base = defaultDatabase();

    const merged = {
      ...base,
      ...parsed
    };

    for (const key of Object.keys(base)) {
      if (
        Array.isArray(base[key]) &&
        !Array.isArray(merged[key])
      ) {
        merged[key] = [];
      }
    }

    if (!merged.dnsStats || typeof merged.dnsStats !== "object") {
      merged.dnsStats = base.dnsStats;
    }

    return merged;
  } catch (error) {
    console.error("Database load failed:", error);

    const backupName =
      `${DB_FILE}.broken-${Date.now()}.json`;

    try {
      if (fs.existsSync(DB_FILE)) {
        fs.copyFileSync(DB_FILE, backupName);
      }
    } catch (_) {}

    return defaultDatabase();
  }
}

let saveTimer = null;

function saveDatabase(database = db) {
  database.settings = database.settings || {};
  database.settings.updatedAt = iso();

  const temp = `${DB_FILE}.tmp`;

  try {
    fs.writeFileSync(
      temp,
      JSON.stringify(database, null, 2),
      "utf8"
    );

    fs.renameSync(temp, DB_FILE);
  } catch (error) {
    console.error("Database save failed:", error);

    try {
      if (fs.existsSync(temp)) {
        fs.unlinkSync(temp);
      }
    } catch (_) {}
  }
}

function saveSoon() {
  if (saveTimer) return;

  saveTimer = setTimeout(() => {
    saveTimer = null;
    saveDatabase();
  }, 500);
}

/* ------------------------------------------------------------------ */
/* General helpers                                                     */
/* ------------------------------------------------------------------ */

function randomId(bytes = 16) {
  return crypto.randomBytes(bytes).toString("hex");
}

function normalizeUsername(username) {
  return String(username || "")
    .trim()
    .toLowerCase();
}

function publicUser(user) {
  if (!user) return null;

  return {
    id: user.id,
    username: user.username,
    role: user.role || "user",
    ageGroup: user.ageGroup,
    avatar: user.avatar || null,
    createdAt: user.createdAt,
    online: isUserOnline(user.id)
  };
}

function getUserById(id) {
  return db.users.find(user => user.id === id) || null;
}

function getUserByUsername(username) {
  const normalized = normalizeUsername(username);

  return db.users.find(
    user => normalizeUsername(user.username) === normalized
  ) || null;
}

function isUserDeleted(user) {
  return !user || user.deleted === true;
}

function isUserBanned(user) {
  return !!(
    user &&
    (
      user.banned === true ||
      db.bannedIps.includes(user.lastIp)
    )
  );
}

function sanitizeText(text, max = RANDOM_MESSAGE_LIMIT) {
  return String(text || "")
    .replace(/\u0000/g, "")
    .trim()
    .slice(0, max);
}

function isValidUsername(username) {
  return /^[A-Za-z0-9_]{3,24}$/.test(username);
}

function isValidEmail(email) {
  if (!email) return true;

  return /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email);
}

function ageGroupForAge(age) {
  const n = Number(age);

  return AGE_GROUPS.find(
    group => n >= group.min && n <= group.max
  ) || null;
}

function ageEligibility(age) {
  const n = Number(age);

  if (!Number.isInteger(n)) {
    return {
      allowed: false,
      reason: "invalid_age"
    };
  }

  if (n < 8) {
    return {
      allowed: false,
      reason: "too_young",
      waitYears: 8 - n
    };
  }

  if (n === 19) {
    return {
      allowed: false,
      reason: "age_group_unavailable"
    };
  }

  if (n > 26) {
    return {
      allowed: false,
      reason: "age_range_unavailable"
    };
  }

  const group = ageGroupForAge(n);

  if (!group) {
    return {
      allowed: false,
      reason: "age_group_unavailable"
    };
  }

  return {
    allowed: true,
    age: n,
    ageGroup: group.id
  };
}

/* ------------------------------------------------------------------ */
/* Passwords                                                           */
/* ------------------------------------------------------------------ */

function hashPassword(password) {
  const salt = crypto.randomBytes(16).toString("hex");

  const hash = crypto.scryptSync(
    String(password),
    salt,
    64
  ).toString("hex");

  return {
    salt,
    hash
  };
}

function verifyPassword(password, user) {
  if (!user || !user.passwordHash || !user.passwordSalt) {
    return false;
  }

  try {
    const hash = crypto.scryptSync(
      String(password),
      user.passwordSalt,
      64
    );

    const stored = Buffer.from(
      user.passwordHash,
      "hex"
    );

    return (
      stored.length === hash.length &&
      crypto.timingSafeEqual(stored, hash)
    );
  } catch (_) {
    return false;
  }
}

/* ------------------------------------------------------------------ */
/* Sessions                                                            */
/* ------------------------------------------------------------------ */

function createSession(user, ip) {
  const token = crypto.randomBytes(48).toString("hex");

  const session = {
    id: randomId(),
    token,
    userId: user.id,
    createdAt: iso(),
    expiresAt: Date.now() + SESSION_MS,
    lastIp: ip || ""
  };

  db.sessions.push(session);

  user.lastIp = ip || user.lastIp || "";
  user.lastSeen = iso();

  saveSoon();

  return token;
}

function removeSession(token) {
  db.sessions = db.sessions.filter(
    session => session.token !== token
  );

  saveSoon();
}

function findSession(token) {
  if (!token) return null;

  const session = db.sessions.find(
    item => item.token === token
  );

  if (!session) return null;

  if (Date.now() > Number(session.expiresAt)) {
    removeSession(token);
    return null;
  }

  return session;
}

function authenticateRequest(req) {
  const header = req.headers.authorization || "";

  let token = "";

  if (header.startsWith("Bearer ")) {
    token = header.slice(7).trim();
  }

  if (!token) {
    const cookie = req.headers.cookie || "";

    const match = cookie.match(
      /(?:^|;\s*)linkup_session=([^;]+)/
    );

    if (match) {
      token = decodeURIComponent(match[1]);
    }
  }

  const session = findSession(token);

  if (!session) return null;

  const user = getUserById(session.userId);

  if (!user || isUserDeleted(user)) {
    return null;
  }

  if (isUserBanned(user)) {
    return null;
  }

  session.lastIp = getClientIp(req);
  user.lastSeen = iso();

  return {
    user,
    session,
    token
  };
}

/* ------------------------------------------------------------------ */
/* Presence                                                            */
/* ------------------------------------------------------------------ */

function isUserOnline(userId) {
  const presence = db.presence.find(
    item =>
      item.userId === userId &&
      Date.now() - Number(item.lastSeen || 0) <=
        PRESENCE_TIMEOUT_MS
  );

  return !!presence;
}

function touchPresence(user, req, gameId = null, consoleName = null) {
  const existing = db.presence.find(
    item => item.userId === user.id
  );

  const timestamp = Date.now();

  if (existing) {
    existing.lastSeen = timestamp;
    existing.ip = getClientIp(req);
    existing.gameId = gameId;
    existing.console = consoleName;
  } else {
    db.presence.push({
      userId: user.id,
      lastSeen: timestamp,
      ip: getClientIp(req),
      gameId,
      console: consoleName
    });
  }

  user.lastSeen = iso(timestamp);

  saveSoon();
}

function cleanupPresence() {
  const cutoff = Date.now() - PRESENCE_TIMEOUT_MS;

  db.presence = db.presence.filter(
    item => Number(item.lastSeen || 0) > cutoff
  );

  saveSoon();
}

/* ------------------------------------------------------------------ */
/* Blocking                                                            */
/* ------------------------------------------------------------------ */

function hasBlocked(userA, userB) {
  return db.blockedUsers.some(
    block =>
      (
        block.blockerId === userA.id &&
        block.blockedId === userB.id
      ) ||
      (
        block.blockerId === userB.id &&
        block.blockedId === userA.id
      )
  );
}

function blockUser(blocker, blocked) {
  if (!blocker || !blocked) return;

  if (blocker.id === blocked.id) {
    return;
  }

  const already = db.blockedUsers.some(
    block =>
      block.blockerId === blocker.id &&
      block.blockedId === blocked.id
  );

  if (!already) {
    db.blockedUsers.push({
      id: randomId(),
      blockerId: blocker.id,
      blockedId: blocked.id,
      createdAt: iso()
    });
  }

  saveSoon();
}

/* ------------------------------------------------------------------ */
/* Chat relationships                                                  */
/* ------------------------------------------------------------------ */

function acceptedChatBetween(userA, userB) {
  return db.chatRequests.some(
    request =>
      request.status === "accepted" &&
      (
        (
          request.fromUserId === userA.id &&
          request.toUserId === userB.id
        ) ||
        (
          request.fromUserId === userB.id &&
          request.toUserId === userA.id
        )
      )
  );
}

function findPendingRequest(userA, userB) {
  return db.chatRequests.find(
    request =>
      request.status === "pending" &&
      (
        (
          request.fromUserId === userA.id &&
          request.toUserId === userB.id
        ) ||
        (
          request.fromUserId === userB.id &&
          request.toUserId === userA.id
        )
      )
  );
}

/* ------------------------------------------------------------------ */
/* Random chat                                                         */
/* ------------------------------------------------------------------ */

function currentRandomChat(userId) {
  const chatId = activeChatByUser.get(userId);

  if (!chatId) return null;

  const chat = randomChats.get(chatId);

  if (!chat) {
    activeChatByUser.delete(userId);
    return null;
  }

  return chat;
}

function otherUserInRandomChat(chat, userId) {
  if (!chat) return null;

  const otherId =
    chat.userA === userId
      ? chat.userB
      : chat.userA === userId
        ? chat.userA
        : null;

  return otherId
    ? getUserById(otherId)
    : null;
}

function removeFromRandomQueue(userId) {
  for (const [group, queuedUserId] of activeRandomQueue.entries()) {
    if (queuedUserId === userId) {
      activeRandomQueue.delete(group);
    }
  }
}

function endRandomChat(chatId, reason = "ended") {
  const chat = randomChats.get(chatId);

  if (!chat) return;

  activeChatByUser.delete(chat.userA);
  activeChatByUser.delete(chat.userB);

  randomChats.delete(chatId);

  logAction(
    "random_chat_end",
    `Random chat ${chatId} ended`,
    {
      chatId,
      reason
    }
  );
}

function kickDuplicateRandomChat(userId, keepChatId = null) {
  const current = currentRandomChat(userId);

  if (!current) return;

  if (keepChatId && current.id === keepChatId) {
    return;
  }

  endRandomChat(
    current.id,
    "duplicate_random_chat"
  );
}

function createRandomChat(userA, userB) {
  kickDuplicateRandomChat(userA.id);
  kickDuplicateRandomChat(userB.id);

  const chat = {
    id: randomId(18),
    userA: userA.id,
    userB: userB.id,
    createdAt: iso(),
    updatedAt: iso(),
    messages: [],
    deletedUserId: null,
    deleteDeadline: null
  };

  randomChats.set(chat.id, chat);

  activeChatByUser.set(
    userA.id,
    chat.id
  );

  activeChatByUser.set(
    userB.id,
    chat.id
  );

  logAction(
    "random_chat_start",
    `Random chat created`,
    {
      chatId: chat.id,
      userA: userA.username,
      userB: userB.username,
      ageGroup: userA.ageGroup
    }
  );

  return chat;
}

function queueForRandomChat(user) {
  const existing = currentRandomChat(user.id);

  if (existing) {
    return {
      state: "already_in_chat",
      chat: randomChatForUser(existing, user)
    };
  }

  removeFromRandomQueue(user.id);

  const group = user.ageGroup;

  const waitingUserId = activeRandomQueue.get(group);

  if (
    waitingUserId &&
    waitingUserId !== user.id
  ) {
    const waitingUser = getUserById(waitingUserId);

    activeRandomQueue.delete(group);

    if (
      waitingUser &&
      !isUserDeleted(waitingUser) &&
      !hasBlocked(user, waitingUser) &&
      !currentRandomChat(waitingUser.id)
    ) {
      const chat = createRandomChat(
        waitingUser,
        user
      );

      return {
        state: "matched",
        chat: randomChatForUser(chat, user)
      };
    }
  }

  activeRandomQueue.set(
    group,
    user.id
  );

  return {
    state: "waiting"
  };
}

function randomChatForUser(chat, user) {
  const otherId =
    chat.userA === user.id
      ? chat.userB
      : chat.userA;

  const other = getUserById(otherId);

  return {
    id: chat.id,
    state: "matched",
    createdAt: chat.createdAt,
    updatedAt: chat.updatedAt,
    otherUser: other
      ? publicUser(other)
      : {
          id: otherId,
          username: "AccountForgotten",
          ageGroup: user.ageGroup,
          online: false
        },
    messages: chat.messages.map(message => ({
      id: message.id,
      senderId: message.senderId,
      senderUsername: message.senderUsername,
      text: message.text,
      createdAt: message.createdAt
    })),
    deletedUserId: chat.deletedUserId,
    deleteDeadline: chat.deleteDeadline
  };
}

function sendRandomMessage(user, chat, text) {
  if (!chat) {
    return {
      ok: false,
      status: 404,
      error: "random_chat_not_found"
    };
  }

  if (
    chat.userA !== user.id &&
    chat.userB !== user.id
  ) {
    return {
      ok: false,
      status: 403,
      error: "not_a_member"
    };
  }

  if (chat.deletedUserId) {
    return {
      ok: false,
      status: 403,
      error: "account_deletion_in_progress"
    };
  }

  const clean = sanitizeText(
    text,
    RANDOM_MESSAGE_LIMIT
  );

  if (!clean) {
    return {
      ok: false,
      status: 400,
      error: "message_required"
    };
  }

  const message = {
    id: randomId(),
    senderId: user.id,
    senderUsername: user.username,
    text: clean,
    createdAt: iso()
  };

  chat.messages.push(message);

  if (chat.messages.length > 200) {
    chat.messages.splice(
      0,
      chat.messages.length - 200
    );
  }

  chat.updatedAt = iso();

  return {
    ok: true,
    message
  };
}

function skipRandomChat(user) {
  const chat = currentRandomChat(user.id);

  if (chat) {
    endRandomChat(
      chat.id,
      "skipped"
    );
  }

  removeFromRandomQueue(user.id);

  return {
    ok: true
  };
}

/* ------------------------------------------------------------------ */
/* Account deletion                                                    */
/* ------------------------------------------------------------------ */

function makeForgottenUsername() {
  return (
    "AccountForgotten(" +
    crypto.randomBytes(10).toString("base64url") +
    ")"
  );
}

function markAccountDeleted(user) {
  if (!user || user.deleted) {
    return;
  }

  user.deleted = true;
  user.deletedAt = iso();
  user.forgottenUsername = makeForgottenUsername();

  /*
    Immediately remove normal login access.
  */
  db.sessions = db.sessions.filter(
    session => session.userId !== user.id
  );

  removeFromRandomQueue(user.id);

  /*
    If the deleted account is in a random chat, the chat remains
    for 18 seconds. The other user sees the replacement name and
    the deletion flag.
  */
  const chat = currentRandomChat(user.id);

  if (chat) {
    chat.deletedUserId = user.id;
    chat.deleteDeadline =
      Date.now() + DELETED_ACCOUNT_DELAY_MS;

    chat.updatedAt = iso();

    const timer = setTimeout(() => {
      const current = randomChats.get(chat.id);

      if (current) {
        endRandomChat(
          chat.id,
          "account_deleted"
        );
      }

      deletedAccountTimers.delete(user.id);
    }, DELETED_ACCOUNT_DELAY_MS);

    deletedAccountTimers.set(
      user.id,
      timer
    );
  }

  /*
    Remove the deleted user's presence.
  */
  db.presence = db.presence.filter(
    item => item.userId !== user.id
  );

  saveSoon();

  logAction(
    "account_deleted",
    `Account ${user.username} was deleted`,
    {
      userId: user.id
    }
  );
}

/* ------------------------------------------------------------------ */
/* Request parsing                                                     */
/* ------------------------------------------------------------------ */

function getClientIp(req) {
  const forwarded = req.headers["x-forwarded-for"];

  if (forwarded) {
    return String(forwarded)
      .split(",")[0]
      .trim();
  }

  return (
    req.socket.remoteAddress ||
    ""
  ).replace(/^::ffff:/, "");
}

function readBody(req) {
  return new Promise((resolve, reject) => {
    let size = 0;
    const chunks = [];

    req.on("data", chunk => {
      size += chunk.length;

      if (size > BODY_LIMIT) {
        reject(
          Object.assign(
            new Error("Request body too large"),
            {
              statusCode: 413
            }
          )
        );

        req.destroy();
        return;
      }

      chunks.push(chunk);
    });

    req.on("end", () => {
      try {
        const raw = Buffer.concat(chunks).toString("utf8");

        if (!raw) {
          resolve({});
          return;
        }

        resolve(JSON.parse(raw));
      } catch (_) {
        reject(
          Object.assign(
            new Error("Invalid JSON"),
            {
              statusCode: 400
            }
          )
        );
      }
    });

    req.on("error", reject);
  });
}

function sendJson(res, status, data, headers = {}) {
  const body = JSON.stringify(data);

  res.writeHead(
    status,
    {
      "Content-Type": "application/json; charset=utf-8",
      "Cache-Control": "no-store",
      "Access-Control-Allow-Origin": "*",
      "Access-Control-Allow-Headers":
        "Content-Type, Authorization",
      "Access-Control-Allow-Methods":
        "GET, POST, PUT, DELETE, OPTIONS",
      ...headers
    }
  );

  res.end(body);
}

function sendText(res, status, text) {
  res.writeHead(
    status,
    {
      "Content-Type": "text/plain; charset=utf-8",
      "Cache-Control": "no-store"
    }
  );

  res.end(text);
}

function requireAuth(req, res) {
  const auth = authenticateRequest(req);

  if (!auth) {
    sendJson(res, 401, {
      ok: false,
      error: "authentication_required"
    });

    return null;
  }

  return auth;
}

/* ------------------------------------------------------------------ */
/* HTTP server                                                         */
/* ------------------------------------------------------------------ */

const httpServer = http.createServer(
  async (req, res) => {
    try {
      if (req.method === "OPTIONS") {
        res.writeHead(204, {
          "Access-Control-Allow-Origin": "*",
          "Access-Control-Allow-Headers":
            "Content-Type, Authorization",
          "Access-Control-Allow-Methods":
            "GET, POST, PUT, DELETE, OPTIONS"
        });

        res.end();
        return;
      }

      const url = new URL(
        req.url,
        `http://${req.headers.host || "localhost"}`
      );

      const pathname = url.pathname;

      /*
        Website
      */
      if (
        req.method === "GET" &&
        (
          pathname === "/" ||
          pathname === "/GotACrush.html"
        )
      ) {
        try {
          const html = fs.readFileSync(
            HTML_FILE,
            "utf8"
          );

          res.writeHead(200, {
            "Content-Type": "text/html; charset=utf-8",
            "Cache-Control": "no-cache"
          });

          res.end(html);
        } catch (error) {
          sendText(
            res,
            500,
            "GotACrush.html could not be loaded."
          );
        }

        return;
      }

      /*
        Health
      */
      if (
        req.method === "GET" &&
        pathname === "/api/health"
      ) {
        sendJson(res, 200, {
          ok: true,
          server: SERVER_NAME,
          status: "online",
          render: IS_RENDER,
          httpsTerminatedByRender: IS_RENDER,
          time: iso()
        });

        return;
      }

      /*
        Status
      */
      if (
        req.method === "GET" &&
        pathname === "/api/status"
      ) {
        const realPlayers = db.users.filter(
          user =>
            !user.deleted &&
            !user.banned &&
            isUserOnline(user.id)
        ).length;

        sendJson(res, 200, {
          ok: true,
          server: SERVER_NAME,
          serverFile: SERVER_FILE,
          dataFile: path.basename(DB_FILE),
          website: "GotACrush.html",
          realPlayers,
          pandaBots: 0,
          supportedConsoles: SUPPORTED_CONSOLES,
          ageGroups: AGE_GROUPS,
          randomTextChat: true,
          randomVoiceChat: false,
          randomVideoChat: false,
          dns: {
            enabled: ENABLE_DNS,
            port: DNS_PORT,
            upstreams: DNS_UPSTREAMS
          },
          time: iso()
        });

        return;
      }

      /*
        Age-group information
      */
      if (
        req.method === "GET" &&
        pathname === "/api/age-groups"
      ) {
        sendJson(res, 200, {
          ok: true,
          groups: AGE_GROUPS,
          notes: [
            "Users must be in the same age group to random chat.",
            "Age 19 is not currently included in an age group.",
            "Users under 8 cannot create accounts."
          ]
        });

        return;
      }

      /*
        Registration
      */
      if (
        req.method === "POST" &&
        pathname === "/api/auth/register"
      ) {
        const body = await readBody(req);

        const username =
          String(body.username || "").trim();

        const email =
          String(body.email || "").trim();

        const password =
          String(body.password || "");

        const confirmPassword =
          String(
            body.confirmPassword ??
            body.confirm_password ??
            ""
          );

        const age = Number(body.age);

        if (!isValidUsername(username)) {
          sendJson(res, 400, {
            ok: false,
            error: "invalid_username",
            message:
              "Username must be 3-24 characters and use only letters, numbers, or underscores."
          });

          return;
        }

        if (!isValidEmail(email)) {
          sendJson(res, 400, {
            ok: false,
            error: "invalid_email"
          });

          return;
        }

        if (password.length < 8) {
          sendJson(res, 400, {
            ok: false,
            error: "password_too_short",
            message:
              "Password must be at least 8 characters."
          });

          return;
        }

        if (password !== confirmPassword) {
          sendJson(res, 400, {
            ok: false,
            error: "passwords_do_not_match"
          });

          return;
        }

        const eligibility =
          ageEligibility(age);

        if (!eligibility.allowed) {
          sendJson(res, 403, {
            ok: false,
            error: eligibility.reason,
            waitYears:
              eligibility.waitYears || 0
          });

          return;
        }

        const existing =
          getUserByUsername(username);

        if (existing && !existing.deleted) {
          sendJson(res, 409, {
            ok: false,
            error: "username_taken"
          });

          return;
        }

        if (
          email &&
          db.users.some(
            user =>
              !user.deleted &&
              user.email &&
              user.email.toLowerCase() ===
                email.toLowerCase()
          )
        ) {
          sendJson(res, 409, {
            ok: false,
            error: "email_already_used"
          });

          return;
        }

        const passwordData =
          hashPassword(password);

        /*
          If an old deleted account has the same username,
          keep the username unique.
        */
        if (existing && existing.deleted) {
          sendJson(res, 409, {
            ok: false,
            error: "username_unavailable"
          });

          return;
        }

        const user = {
          id: randomId(18),
          username,
          usernameLower:
            username.toLowerCase(),

          email: email || null,

          age,
          ageGroup: eligibility.ageGroup,

          passwordHash:
            passwordData.hash,

          passwordSalt:
            passwordData.salt,

          role: "user",

          avatar: null,

          createdAt: iso(),
          lastSeen: iso(),

          deleted: false,
          banned: false
        };

        db.users.push(user);

        const token = createSession(
          user,
          getClientIp(req)
        );

        logAction(
          "account_created",
          `Account ${username} created`,
          {
            userId: user.id,
            ageGroup: user.ageGroup
          }
        );

        sendJson(
          res,
          201,
          {
            ok: true,
            user: publicUser(user),
            token
          },
          {
            "Set-Cookie":
              `linkup_session=${encodeURIComponent(token)}; HttpOnly; SameSite=Lax; Max-Age=${SESSION_DAYS * 86400}${COOKIE_SECURE}`
          }
        );

        return;
      }

      /*
        Login
      */
      if (
        req.method === "POST" &&
        pathname === "/api/auth/login"
      ) {
        const body = await readBody(req);

        const username =
          String(body.username || "").trim();

        const password =
          String(body.password || "");

        const user =
          getUserByUsername(username);

        if (
          !user ||
          user.deleted ||
          !verifyPassword(password, user)
        ) {
          sendJson(res, 401, {
            ok: false,
            error: "invalid_login"
          });

          return;
        }

        if (isUserBanned(user)) {
          sendJson(res, 403, {
            ok: false,
            error: "account_banned"
          });

          return;
        }

        const token = createSession(
          user,
          getClientIp(req)
        );

        sendJson(
          res,
          200,
          {
            ok: true,
            user: publicUser(user),
            token
          },
          {
            "Set-Cookie":
              `linkup_session=${encodeURIComponent(token)}; HttpOnly; SameSite=Lax; Max-Age=${SESSION_DAYS * 86400}${COOKIE_SECURE}`
          }
        );

        return;
      }

      /*
        Logout
      */
      if (
        req.method === "POST" &&
        pathname === "/api/auth/logout"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        removeSession(auth.token);

        sendJson(
          res,
          200,
          { ok: true },
          {
            "Set-Cookie":
              "linkup_session=; HttpOnly; SameSite=Lax; Max-Age=0" + COOKIE_SECURE
          }
        );

        return;
      }

      /*
        Current account
      */
      if (
        req.method === "GET" &&
        pathname === "/api/auth/me"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        sendJson(res, 200, {
          ok: true,
          user: publicUser(auth.user)
        });

        return;
      }

      /*
        Change password
      */
      if (
        req.method === "POST" &&
        pathname === "/api/account/password"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const currentPassword =
          String(body.currentPassword || "");

        const newPassword =
          String(body.newPassword || "");

        const confirmPassword =
          String(
            body.confirmPassword ||
            ""
          );

        if (
          !verifyPassword(
            currentPassword,
            auth.user
          )
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "current_password_incorrect"
          });

          return;
        }

        if (newPassword.length < 8) {
          sendJson(res, 400, {
            ok: false,
            error: "password_too_short"
          });

          return;
        }

        if (newPassword !== confirmPassword) {
          sendJson(res, 400, {
            ok: false,
            error: "passwords_do_not_match"
          });

          return;
        }

        const passwordData =
          hashPassword(newPassword);

        auth.user.passwordHash =
          passwordData.hash;

        auth.user.passwordSalt =
          passwordData.salt;

        /*
          Force other sessions out.
        */
        db.sessions = db.sessions.filter(
          session =>
            session.userId !==
              auth.user.id ||
            session.token === auth.token
        );

        saveSoon();

        sendJson(res, 200, {
          ok: true,
          message: "Password changed."
        });

        return;
      }

      /*
        Change username
      */
      if (
        req.method === "POST" &&
        pathname === "/api/account/username"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const newUsername =
          String(
            body.username || ""
          ).trim();

        if (!isValidUsername(newUsername)) {
          sendJson(res, 400, {
            ok: false,
            error: "invalid_username"
          });

          return;
        }

        const existing =
          getUserByUsername(newUsername);

        if (
          existing &&
          existing.id !== auth.user.id &&
          !existing.deleted
        ) {
          sendJson(res, 409, {
            ok: false,
            error: "username_taken"
          });

          return;
        }

        const oldUsername =
          auth.user.username;

        auth.user.username =
          newUsername;

        auth.user.usernameLower =
          newUsername.toLowerCase();

        saveSoon();

        logAction(
          "username_changed",
          `${oldUsername} changed username to ${newUsername}`,
          {
            userId: auth.user.id
          }
        );

        sendJson(res, 200, {
          ok: true,
          user: publicUser(auth.user)
        });

        return;
      }

      /*
        Delete account
      */
      if (
        req.method === "POST" &&
        pathname === "/api/account/delete"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const password =
          String(body.password || "");

        if (
          !verifyPassword(
            password,
            auth.user
          )
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "password_incorrect"
          });

          return;
        }

        const username =
          auth.user.username;

        markAccountDeleted(
          auth.user
        );

        sendJson(
          res,
          200,
          {
            ok: true,
            deleted: true,
            message:
              "Account deletion started."
          },
          {
            "Set-Cookie":
              "linkup_session=; HttpOnly; SameSite=Lax; Max-Age=0" + COOKIE_SECURE
          }
        );

        logAction(
          "account_delete_request",
          `${username} deleted their account`,
          {
            userId: auth.user.id
          }
        );

        return;
      }

      /*
        Search users
      */
      if (
        req.method === "GET" &&
        pathname === "/api/users/search"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const q =
          String(
            url.searchParams.get("q") || ""
          )
            .trim()
            .toLowerCase();

        if (q.length < 1) {
          sendJson(res, 200, {
            ok: true,
            users: []
          });

          return;
        }

        const users = db.users
          .filter(
            user =>
              !user.deleted &&
              !user.banned &&
              user.ageGroup === auth.user.ageGroup &&
              user.id !== auth.user.id &&
              !hasBlocked(auth.user, user) &&
              normalizeUsername(
                user.username
              ).includes(q)
          )
          .slice(0, 25)
          .map(publicUser);

        sendJson(res, 200, {
          ok: true,
          users
        });

        return;
      }

      /*
        Send chat request
      */
      if (
        req.method === "POST" &&
        pathname === "/api/chat/requests"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const username =
          String(
            body.username || ""
          ).trim();

        const target =
          getUserByUsername(username);

        if (!target || target.deleted) {
          sendJson(res, 404, {
            ok: false,
            error: "user_not_found"
          });

          return;
        }

        if (target.id === auth.user.id) {
          sendJson(res, 400, {
            ok: false,
            error: "cannot_request_self"
          });

          return;
        }

        if (
          target.ageGroup !==
          auth.user.ageGroup
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "different_age_group"
          });

          return;
        }

        if (
          hasBlocked(
            auth.user,
            target
          )
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "user_blocked"
          });

          return;
        }

        if (
          acceptedChatBetween(
            auth.user,
            target
          )
        ) {
          sendJson(res, 409, {
            ok: false,
            error: "already_connected"
          });

          return;
        }

        if (
          findPendingRequest(
            auth.user,
            target
          )
        ) {
          sendJson(res, 409, {
            ok: false,
            error: "request_already_exists"
          });

          return;
        }

        const request = {
          id: randomId(),
          fromUserId: auth.user.id,
          fromUsername: auth.user.username,
          toUserId: target.id,
          toUsername: target.username,
          ageGroup: auth.user.ageGroup,
          status: "pending",
          createdAt: iso(),
          respondedAt: null
        };

        db.chatRequests.push(request);

        saveSoon();

        sendJson(res, 201, {
          ok: true,
          request: {
            id: request.id,
            to: publicUser(target),
            status: request.status,
            createdAt: request.createdAt
          }
        });

        return;
      }

      /*
        Get requests
      */
      if (
        req.method === "GET" &&
        pathname === "/api/chat/requests"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const requests =
          db.chatRequests
            .filter(
              request =>
                request.fromUserId === auth.user.id ||
                request.toUserId === auth.user.id
            )
            .map(request => {
              const incoming =
                request.toUserId ===
                auth.user.id;

              const other =
                getUserById(
                  incoming
                    ? request.fromUserId
                    : request.toUserId
                );

              return {
                id: request.id,
                direction:
                  incoming
                    ? "incoming"
                    : "outgoing",
                status: request.status,
                createdAt:
                  request.createdAt,
                respondedAt:
                  request.respondedAt,
                user: other
                  ? publicUser(other)
                  : {
                      username:
                        "AccountForgotten"
                    }
              };
            });

        sendJson(res, 200, {
          ok: true,
          requests
        });

        return;
      }

      /*
        Accept/decline request
      */
      if (
        req.method === "POST" &&
        pathname === "/api/chat/requests/respond"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const requestId =
          String(body.requestId || "");

        const action =
          String(body.action || "")
            .toLowerCase();

        const request =
          db.chatRequests.find(
            item =>
              item.id === requestId
          );

        if (!request) {
          sendJson(res, 404, {
            ok: false,
            error: "request_not_found"
          });

          return;
        }

        if (
          request.toUserId !==
          auth.user.id
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "not_request_recipient"
          });

          return;
        }

        if (request.status !== "pending") {
          sendJson(res, 409, {
            ok: false,
            error: "request_already_handled"
          });

          return;
        }

        if (
          action !== "accept" &&
          action !== "decline"
        ) {
          sendJson(res, 400, {
            ok: false,
            error: "invalid_action"
          });

          return;
        }

        const sender =
          getUserById(
            request.fromUserId
          );

        if (!sender || sender.deleted) {
          request.status = "declined";
        } else if (
          action === "accept" &&
          sender.ageGroup ===
            auth.user.ageGroup &&
          !hasBlocked(
            auth.user,
            sender
          )
        ) {
          request.status = "accepted";
        } else {
          request.status = "declined";
        }

        request.respondedAt =
          iso();

        saveSoon();

        sendJson(res, 200, {
          ok: true,
          request: {
            id: request.id,
            status: request.status
          }
        });

        return;
      }

      /*
        List accepted chats
      */
      if (
        req.method === "GET" &&
        pathname === "/api/chats"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const chats = [];

        for (const request of db.chatRequests) {
          if (
            request.status !==
            "accepted"
          ) {
            continue;
          }

          let otherId = null;

          if (
            request.fromUserId ===
            auth.user.id
          ) {
            otherId =
              request.toUserId;
          } else if (
            request.toUserId ===
            auth.user.id
          ) {
            otherId =
              request.fromUserId;
          }

          if (!otherId) continue;

          const other =
            getUserById(otherId);

          if (
            !other ||
            other.deleted
          ) {
            continue;
          }

          if (
            hasBlocked(
              auth.user,
              other
            )
          ) {
            continue;
          }

          chats.push({
            id: request.id,
            user: publicUser(other)
          });
        }

        sendJson(res, 200, {
          ok: true,
          chats
        });

        return;
      }

      /*
        Normal accepted-user chat
      */
      if (
        req.method === "POST" &&
        pathname === "/api/chat/send"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const username =
          String(
            body.username || ""
          ).trim();

        const target =
          getUserByUsername(username);

        if (!target || target.deleted) {
          sendJson(res, 404, {
            ok: false,
            error: "user_not_found"
          });

          return;
        }

        if (
          target.ageGroup !==
          auth.user.ageGroup
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "different_age_group"
          });

          return;
        }

        if (
          hasBlocked(
            auth.user,
            target
          )
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "user_blocked"
          });

          return;
        }

        if (
          !acceptedChatBetween(
            auth.user,
            target
          )
        ) {
          sendJson(res, 403, {
            ok: false,
            error:
              "chat_request_not_accepted"
          });

          return;
        }

        const text =
          sanitizeText(
            body.text,
            RANDOM_MESSAGE_LIMIT
          );

        if (!text) {
          sendJson(res, 400, {
            ok: false,
            error: "message_required"
          });

          return;
        }

        const message = {
          id: randomId(),
          fromUserId:
            auth.user.id,
          fromUsername:
            auth.user.username,
          toUserId:
            target.id,
          toUsername:
            target.username,
          text,
          createdAt: iso()
        };

        db.messages.push(message);

        saveSoon();

        sendJson(res, 201, {
          ok: true,
          message
        });

        return;
      }

      /*
        Read accepted-user chat
      */
      if (
        req.method === "GET" &&
        pathname.startsWith("/api/chat/")
      ) {
        const username =
          decodeURIComponent(
            pathname.slice(
              "/api/chat/".length
            )
          );

        if (
          username === "requests" ||
          username === "send"
        ) {
          sendJson(res, 404, {
            ok: false,
            error: "not_found"
          });

          return;
        }

        const auth = requireAuth(req, res);

        if (!auth) return;

        const target =
          getUserByUsername(username);

        if (!target || target.deleted) {
          sendJson(res, 404, {
            ok: false,
            error: "user_not_found"
          });

          return;
        }

        if (
          target.ageGroup !==
          auth.user.ageGroup
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "different_age_group"
          });

          return;
        }

        if (
          !acceptedChatBetween(
            auth.user,
            target
          )
        ) {
          sendJson(res, 403, {
            ok: false,
            error:
              "chat_request_not_accepted"
          });

          return;
        }

        const messages =
          db.messages.filter(
            message =>
              (
                message.fromUserId ===
                  auth.user.id &&
                message.toUserId ===
                  target.id
              ) ||
              (
                message.fromUserId ===
                  target.id &&
                message.toUserId ===
                  auth.user.id
              )
          ).slice(-100);

        sendJson(res, 200, {
          ok: true,
          user: publicUser(target),
          messages
        });

        return;
      }

      /*
        Block user
      */
      if (
        req.method === "POST" &&
        pathname === "/api/users/block"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const target =
          getUserByUsername(
            String(
              body.username || ""
            ).trim()
          );

        if (!target) {
          sendJson(res, 404, {
            ok: false,
            error: "user_not_found"
          });

          return;
        }

        if (
          target.id ===
          auth.user.id
        ) {
          sendJson(res, 400, {
            ok: false,
            error: "cannot_block_self"
          });

          return;
        }

        blockUser(
          auth.user,
          target
        );

        /*
          Also stop an active random chat.
        */
        const randomChat =
          currentRandomChat(
            auth.user.id
          );

        if (
          randomChat &&
          (
            randomChat.userA ===
              target.id ||
            randomChat.userB ===
              target.id
          )
        ) {
          endRandomChat(
            randomChat.id,
            "blocked"
          );
        }

        sendJson(res, 200, {
          ok: true
        });

        return;
      }

      /*
        Report user
      */
      if (
        req.method === "POST" &&
        pathname === "/api/users/report"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const target =
          getUserByUsername(
            String(
              body.username || ""
            ).trim()
          );

        if (!target) {
          sendJson(res, 404, {
            ok: false,
            error: "user_not_found"
          });

          return;
        }

        const reason =
          sanitizeText(
            body.reason,
            500
          );

        db.reports.push({
          id: randomId(),
          reporterId:
            auth.user.id,
          reporterUsername:
            auth.user.username,
          reportedUserId:
            target.id,
          reportedUsername:
            target.username,
          reason,
          createdAt: iso(),
          status: "open"
        });

        saveSoon();

        sendJson(res, 201, {
          ok: true,
          message:
            "Report submitted."
        });

        return;
      }

      /*
        Presence
      */
      if (
        req.method === "POST" &&
        pathname === "/api/presence"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        touchPresence(
          auth.user,
          req,
          body.gameId ?? null,
          body.console ?? null
        );

        sendJson(res, 200, {
          ok: true,
          online: true
        });

        return;
      }

      /*
        Player count
      */
      if (
        req.method === "GET" &&
        pathname === "/api/players"
      ) {
        cleanupPresence();

        const realPlayers =
          db.users.filter(
            user =>
              !user.deleted &&
              !user.banned &&
              isUserOnline(user.id)
          ).length;

        sendJson(res, 200, {
          ok: true,
          realPlayers,
          pandaBots: 0,
          totalPlayers: realPlayers
        });

        return;
      }

      /*
        Join random text chat
      */
      if (
        req.method === "POST" &&
        pathname === "/api/random/join"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        touchPresence(
          auth.user,
          req
        );

        const result =
          queueForRandomChat(
            auth.user
          );

        sendJson(res, 200, {
          ok: true,
          ...result
        });

        return;
      }

      /*
        Random chat status
      */
      if (
        req.method === "GET" &&
        pathname === "/api/random/status"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const chat =
          currentRandomChat(
            auth.user.id
          );

        if (!chat) {
          const queued =
            activeRandomQueue.get(
              auth.user.ageGroup
            ) === auth.user.id;

          sendJson(res, 200, {
            ok: true,
            state: queued
              ? "waiting"
              : "idle"
          });

          return;
        }

        /*
          Duplicate protection.
          If something ever causes the same user to appear
          in another random chat, this request ends the
          older chat.
        */
        const duplicateChats = [];

        for (const [
          chatId,
          candidate
        ] of randomChats.entries()) {
          if (
            chatId !== chat.id &&
            (
              candidate.userA ===
                auth.user.id ||
              candidate.userB ===
                auth.user.id
            )
          ) {
            duplicateChats.push(
              chatId
            );
          }
        }

        for (const chatId of duplicateChats) {
          endRandomChat(
            chatId,
            "duplicate_user_detected"
          );
        }

        sendJson(res, 200, {
          ok: true,
          state: "matched",
          chat:
            randomChatForUser(
              chat,
              auth.user
            )
        });

        return;
      }

      /*
        Send random message
      */
      if (
        req.method === "POST" &&
        pathname === "/api/random/message"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const chatId =
          String(
            body.chatId || ""
          );

        const chat =
          randomChats.get(chatId);

        const result =
          sendRandomMessage(
            auth.user,
            chat,
            body.text
          );

        if (!result.ok) {
          sendJson(
            res,
            result.status,
            result
          );

          return;
        }

        sendJson(res, 201, result);

        return;
      }

      /*
        Skip random user
      */
      if (
        req.method === "POST" &&
        pathname === "/api/random/skip"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const result =
          skipRandomChat(
            auth.user
          );

        /*
          Immediately put them back into
          the queue if they requested that.
        */
        const joinAgain =
          Boolean(
            (
              await readBody(req)
            ).joinAgain
          );

        if (joinAgain) {
          const queue =
            queueForRandomChat(
              auth.user
            );

          sendJson(res, 200, {
            ...result,
            ...queue
          });

          return;
        }

        sendJson(res, 200, result);

        return;
      }

      /*
        Random block
      */
      if (
        req.method === "POST" &&
        pathname === "/api/random/block"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        const body = await readBody(req);

        const chatId =
          String(
            body.chatId || ""
          );

        const chat =
          randomChats.get(chatId);

        if (!chat) {
          sendJson(res, 404, {
            ok: false,
            error: "random_chat_not_found"
          });

          return;
        }

        if (
          chat.userA !==
            auth.user.id &&
          chat.userB !==
            auth.user.id
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "not_a_member"
          });

          return;
        }

        const otherId =
          chat.userA === auth.user.id
            ? chat.userB
            : chat.userA;

        const other =
          getUserById(otherId);

        if (other) {
          blockUser(
            auth.user,
            other
          );
        }

        endRandomChat(
          chat.id,
          "blocked"
        );

        sendJson(res, 200, {
          ok: true
        });

        return;
      }

      /*
        Random leave
      */
      if (
        req.method === "POST" &&
        pathname === "/api/random/leave"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        removeFromRandomQueue(
          auth.user.id
        );

        const chat =
          currentRandomChat(
            auth.user.id
          );

        if (chat) {
          endRandomChat(
            chat.id,
            "left"
          );
        }

        sendJson(res, 200, {
          ok: true
        });

        return;
      }

      /*
        DNS/admin status
      */
      if (
        req.method === "GET" &&
        pathname === "/api/dns/status"
      ) {
        sendJson(res, 200, {
          ok: true,
          enabled: true,
          port: DNS_PORT,
          upstreams: DNS_UPSTREAMS,
          totalQueries:
            db.dnsStats.totalQueries,
          blockedQueries:
            db.dnsStats.blockedQueries,
          forwardedQueries:
            db.dnsStats.forwardedQueries
        });

        return;
      }

      /*
        Admin event log.
        Kept simple and protected by owner username.
      */
      if (
        req.method === "GET" &&
        pathname === "/api/admin/events"
      ) {
        const auth = requireAuth(req, res);

        if (!auth) return;

        if (
          auth.user.username !==
          ADMIN_OWNER
        ) {
          sendJson(res, 403, {
            ok: false,
            error: "admin_required"
          });

          return;
        }

        sendJson(res, 200, {
          ok: true,
          events: eventLogs,
          actions: actionLogs
        });

        return;
      }

      sendJson(res, 404, {
        ok: false,
        error: "not_found"
      });
    } catch (error) {
      console.error(
        "HTTP request error:",
        error
      );

      if (!res.headersSent) {
        sendJson(res, 500, {
          ok: false,
          error: "server_error"
        });
      }
    }
  }
);

/* ------------------------------------------------------------------ */
/* DNS                                                                 */
/* ------------------------------------------------------------------ */

function cleanDomain(name) {
  return String(name || "")
    .toLowerCase()
    .replace(/\.$/, "")
    .trim();
}

function domainMatches(domain, allowed) {
  const d = cleanDomain(domain);
  const a = cleanDomain(allowed);

  return (
    d === a ||
    d.endsWith("." + a)
  );
}

function isDomainAllowed(domain) {
  const normalized =
    cleanDomain(domain);

  for (
    const allowed
    of PERMANENT_ALLOWED_DOMAINS
  ) {
    if (
      domainMatches(
        normalized,
        allowed
      )
    ) {
      return true;
    }
  }

  for (
    const allowed
    of db.allowedDomainsExtra || []
  ) {
    if (
      domainMatches(
        normalized,
        allowed
      )
    ) {
      return true;
    }
  }

  return false;
}

function isDomainBanned(domain) {
  const normalized =
    cleanDomain(domain);

  for (
    const banned
    of HARD_BANNED_DOMAINS
  ) {
    if (
      domainMatches(
        normalized,
        banned
      )
    ) {
      return true;
    }
  }

  for (
    const banned
    of db.bannedDomains || []
  ) {
    if (
      domainMatches(
        normalized,
        banned
      )
    ) {
      return true;
    }
  }

  for (
    const keyword
    of BANNED_KEYWORDS
  ) {
    if (
      normalized.includes(
        keyword
      )
    ) {
      return true;
    }
  }

  return false;
}

function parseDnsQuestion(message) {
  if (
    !Buffer.isBuffer(message) ||
    message.length < 12
  ) {
    return null;
  }

  const transactionId =
    message.subarray(0, 2);

  let offset = 12;
  const labels = [];

  try {
    while (offset < message.length) {
      const length =
        message[offset++];

      if (length === 0) break;

      if (
        length > 63 ||
        offset + length >
          message.length
      ) {
        return null;
      }

      labels.push(
        message
          .subarray(
            offset,
            offset + length
          )
          .toString("utf8")
      );

      offset += length;
    }

    if (
      offset + 4 >
      message.length
    ) {
      return null;
    }

    const qtype =
      message.readUInt16BE(offset);

    const qclass =
      message.readUInt16BE(offset + 2);

    return {
      transactionId,
      domain:
        labels.join("."),
      qtype,
      qclass,
      questionEnd:
        offset + 4
    };
  } catch (_) {
    return null;
  }
}

function buildDnsErrorResponse(
  request,
  rcode
) {
  if (!request || request.length < 12) {
    return null;
  }

  const question =
    parseDnsQuestion(request);

  if (!question) {
    return null;
  }

  const header =
    Buffer.alloc(12);

  request.copy(
    header,
    0,
    0,
    2
  );

  /*
    QR=1
    RD copied
    RA=1
    RCODE supplied
  */
  const originalFlags =
    request.readUInt16BE(2);

  let flags =
    0x8000 |
    0x0080 |
    (originalFlags & 0x0100);

  flags |=
    (rcode & 0x0f);

  header.writeUInt16BE(
    flags,
    2
  );

  header.writeUInt16BE(
    1,
    4
  );

  header.writeUInt16BE(
    0,
    6
  );

  header.writeUInt16BE(
    0,
    8
  );

  header.writeUInt16BE(
    0,
    10
  );

  return Buffer.concat([
    header,
    request.subarray(
      12,
      question.questionEnd
    )
  ]);
}

function checkDnsRateLimit(ip) {
  const timestamp =
    Date.now();

  let record =
    dnsRate.get(ip);

  if (!record) {
    record = {
      startedAt: timestamp,
      count: 0
    };

    dnsRate.set(
      ip,
      record
    );
  }

  if (
    timestamp -
      record.startedAt >
    DNS_RATE_WINDOW_MS
  ) {
    record.startedAt =
      timestamp;

    record.count = 0;
  }

  record.count++;

  return (
    record.count <=
    DNS_RATE_MAX
  );
}

function forwardDns(
  message,
  client,
  server
) {
  const upstream =
    DNS_UPSTREAMS[
      Math.floor(
        Math.random() *
          DNS_UPSTREAMS.length
      )
    ];

  const socket =
    dgram.createSocket("udp4");

  let completed = false;

  const finish = () => {
    if (completed) return;

    completed = true;

    try {
      socket.close();
    } catch (_) {}
  };

  socket.once(
    "message",
    response => {
      if (completed) return;

      try {
        server.send(
          response,
          client.port,
          client.address
        );
      } catch (_) {}

      db.dnsStats.forwardedQueries++;

      finish();
    }
  );

  socket.once(
    "error",
    error => {
      logDns(
        "DNS upstream error",
        {
          upstream,
          error:
            error.message
        }
      );

      finish();
    }
  );

  socket.send(
    message,
    53,
    upstream,
    error => {
      if (error) {
        logDns(
          "DNS send failed",
          {
            upstream,
            error:
              error.message
          }
        );

        finish();
      }
    }
  );

  setTimeout(() => {
    if (!completed) {
      finish();
    }
  }, 2500);
}

const dnsServer =
  dgram.createSocket("udp4");

dnsServer.on(
  "message",
  (message, client) => {
    const ip =
      client.address;

    db.dnsStats.totalQueries++;

    if (
      db.bannedIps &&
      db.bannedIps.includes(ip)
    ) {
      logDns(
        "Blocked DNS request from banned IP",
        { ip }
      );

      return;
    }

    if (
      !checkDnsRateLimit(ip)
    ) {
      logDns(
        "DNS rate limit exceeded",
        { ip }
      );

      const response =
        buildDnsErrorResponse(
          message,
          5
        );

      if (response) {
        dnsServer.send(
          response,
          client.port,
          client.address
        );
      }

      return;
    }

    const question =
      parseDnsQuestion(message);

    if (!question) {
      return;
    }

    const domain =
      cleanDomain(
        question.domain
      );

    logDns(
      "DNS query",
      {
        ip,
        domain,
        qtype:
          question.qtype
      }
    );

    if (
      isDomainBanned(domain) &&
      !isDomainAllowed(domain)
    ) {
      db.dnsStats.blockedQueries++;

      const response =
        buildDnsErrorResponse(
          message,
          3
        );

      if (response) {
        dnsServer.send(
          response,
          client.port,
          client.address
        );
      }

      return;
    }

    forwardDns(
      message,
      client,
      dnsServer
    );
  }
);

dnsServer.on(
  "error",
  error => {
    logEvent(
      "dns_error",
      error.message
    );
  }
);

/* ------------------------------------------------------------------ */
/* POWER 2 - LittleBigPlanet 3 subsystem                              */
/* ------------------------------------------------------------------ */

function lbp3NowId() {
  return crypto.randomBytes(3).toString("hex").toUpperCase();
}

function lbp3Nonce() {
  return crypto.randomBytes(24).toString("hex");
}

function lbp3ClientIp(socketOrReq) {
  const raw =
    socketOrReq?.socket?.remoteAddress ||
    socketOrReq?.remoteAddress ||
    "unknown";

  return String(raw).replace(/^::ffff:/, "");
}

function lbp3SafeHeaders(req) {
  return {
    host: String(req.headers.host || "unknown").slice(0, 255),
    method: req.method,
    path: String(req.url || "/").slice(0, 2048),
    requestId: String(req.headers["x-linkup-request-id"] || ""),
    timestamp: String(req.headers["x-linkup-timestamp"] || ""),
    noncePresent: Boolean(req.headers["x-linkup-nonce"])
  };
}

function lbp3Log(type, message, data = {}) {
  const clean = { ...data };

  /* Never put passwords, cookies, session tokens or nonces in logs. */
  delete clean.password;
  delete clean.passwordHash;
  delete clean.passwordSalt;
  delete clean.authorization;
  delete clean.cookie;
  delete clean.session;
  delete clean.token;
  delete clean.nonce;

  console.log(`[LBP3 ${type}] ${message}`, clean);
}

function lbp3Decline(id, clientIp, reason, status = 403) {
  lbp3Power.declinedCount++;
  if (reason === "replay" || reason === "rate_limit") {
    lbp3Power.blockedCount++;
  }

  console.log(
    `\n[DECLINED ${id}]\n` +
    `CLIENT: ${clientIp}\n` +
    `STATUS: ${status}\n` +
    `REASON: ${reason}\n` +
    `RESULT: BLOCKED\n`
  );
}

function lbp3CheckRate(clientIp) {
  const now = Date.now();
  let record = lbp3Power.security.rate.get(clientIp);

  if (!record || now - record.startedAt > LBP3_RATE_WINDOW_MS) {
    record = { startedAt: now, count: 0 };
    lbp3Power.security.rate.set(clientIp, record);
  }

  record.count++;
  return record.count <= LBP3_RATE_MAX;
}

function lbp3VerifySecurity(req, clientIp, requestId) {
  const timestampRaw = String(req.headers["x-linkup-timestamp"] || "");
  const nonce = String(req.headers["x-linkup-nonce"] || "");
  const timestamp = Number(timestampRaw);

  if (!/^[A-Fa-f0-9]{12}$/.test(requestId)) {
    return { ok: false, reason: "invalid_request_id" };
  }

  if (!Number.isFinite(timestamp) || Math.abs(Date.now() - timestamp) > LBP3_REQUEST_MAX_AGE_MS) {
    return { ok: false, reason: "stale_timestamp" };
  }

  if (!/^[A-Fa-f0-9]{48}$/.test(nonce)) {
    return { ok: false, reason: "invalid_nonce" };
  }

  const previous = lbp3Power.security.usedNonces.get(nonce);
  if (previous) {
    return { ok: false, reason: "replay" };
  }

  /* Bind the nonce to the client address for this server instance. */
  lbp3Power.security.usedNonces.set(nonce, {
    clientIp,
    requestId,
    expiresAt: Date.now() + LBP3_NONCE_TTL_MS
  });

  return { ok: true };
}

function lbp3SendJson(res, status, body, requestId) {
  const payload = JSON.stringify(body);

  res.writeHead(status, {
    "Content-Type": "application/json; charset=utf-8",
    "Content-Length": Buffer.byteLength(payload),
    "Cache-Control": "no-store",
    "X-LinkUp-Request-ID": requestId
  });

  res.end(payload);
}

function lbp3HandleRequest(req, res) {
  const id = String(req.headers["x-linkup-request-id"] || lbp3NowId());
  const clientIp = lbp3ClientIp(req);
  const safe = lbp3SafeHeaders(req);

  lbp3Power.requestCount++;

  console.log(
    `\n[LBP3 REQUEST ${id}]\n` +
    `CLIENT: ${clientIp}\n` +
    `HOST: ${safe.host}\n` +
    `METHOD: ${safe.method}\n` +
    `PATH: ${safe.path}\n` +
    `STATUS: RECEIVED\n`
  );

  if (!lbp3CheckRate(clientIp)) {
    lbp3Decline(id, clientIp, "rate_limit", 429);
    lbp3SendJson(res, 429, { ok: false, error: "rate_limited" }, id);
    return;
  }

  const security = lbp3VerifySecurity(
    req,
    clientIp,
    id
  );

  console.log(
    `[SECURITY ${id}]\n` +
    `✓ Request ID: ${security.ok ? "valid" : "checked"}\n` +
    `✓ Session: isolated from Power 1\n` +
    `✓ Nonce: ${security.ok ? "accepted" : "declined"}\n` +
    `✓ Timestamp: ${security.ok ? "fresh" : security.reason}\n` +
    `✓ Replay check: ${security.ok ? "passed" : security.reason}\n`
  );

  if (!security.ok) {
    lbp3Decline(id, clientIp, security.reason, 403);
    lbp3SendJson(res, 403, { ok: false, error: security.reason }, id);
    return;
  }

  if (req.method === "GET" && req.url === "/health") {
    lbp3Power.successCount++;
    lbp3SendJson(res, 200, {
      ok: true,
      subsystem: "lbp3",
      power: 2,
      ip: SERVER_IP,
      service: "online"
    }, id);

    console.log(
      `\n[LBP3 RESPONSE ${id}]\nSTATUS: 200\nBYTES: health\nRESULT: SUCCESS\n`
    );
    return;
  }

  if (req.method === "GET" && req.url === "/lbp3/status") {
    lbp3Power.successCount++;
    lbp3SendJson(res, 200, {
      ok: true,
      power: 2,
      service: "LittleBigPlanet 3",
      tcpTransport: lbp3Power.online,
      serviceApi: lbp3Power.serviceOnline
    }, id);

    console.log(
      `\n[LBP3 RESPONSE ${id}]\nSTATUS: 200\nBYTES: status\nRESULT: SUCCESS\n`
    );
    return;
  }

  lbp3Power.successCount++;
  lbp3SendJson(res, 404, {
    ok: false,
    error: "lbp3_endpoint_not_implemented"
  }, id);

  console.log(
    `\n[LBP3 RESPONSE ${id}]\nSTATUS: 404\nBYTES: 0\nRESULT: ENDPOINT NOT IMPLEMENTED\n`
  );
}

const lbp3ServiceServer = http.createServer(
  (req, res) => {
    try {
      lbp3HandleRequest(req, res);
    } catch (error) {
      lbp3Power.failureCount++;
      const id = lbp3NowId();
      lbp3Log("FAILURE", "LBP3 service exception", {
        id,
        error: error.message
      });
      try {
        lbp3SendJson(res, 500, { ok: false, error: "service_failure" }, id);
      } catch (_) {}
    }
  }
);

lbp3ServiceServer.on("error", error => {
  lbp3Power.serviceOnline = false;
  lbp3Power.failureCount++;
  lbp3Log("FAILURE", "Power 2 service listener error", {
    error: error.message,
    port: LBP3_SERVICE_PORT
  });
});

const lbp3TcpServer = net.createServer(socket => {
  const id = lbp3NowId();
  const clientIp = lbp3ClientIp(socket);
  let firstPacket = true;

  console.log(
    `\n[LBP3 REQUEST ${id}]\nCLIENT: ${clientIp}\nHOST: ${SERVER_IP}:${LBP3_TCP_PORT}\nMETHOD: TCP\nPATH: /\nSTATUS: RECEIVED\n`
  );

  socket.on("data", data => {
    const preview = data.subarray(0, LBP3_MAX_PACKET_LOG_BYTES).toString("hex");
    const tlsLike = data.length >= 3 && data[0] === 0x16 && data[1] === 0x03;

    lbp3Log("TRANSPORT", "Power 2 received LBP3 transport data", {
      id,
      clientIp,
      bytes: data.length,
      firstPacket,
      tlsLike,
      preview
    });

    firstPacket = false;
  });

  socket.on("error", error => {
    lbp3Power.failureCount++;
    lbp3Log("FAILURE", "LBP3 transport socket error", {
      id,
      clientIp,
      error: error.message
    });
  });

  socket.on("close", () => {
    console.log(
      `\n[LBP3 RESPONSE ${id}]\nSTATUS: CONNECTION CLOSED\nRESULT: TRANSPORT ENDED\n`
    );
  });
});

lbp3TcpServer.on("error", error => {
  lbp3Power.online = false;
  lbp3Power.failureCount++;
  lbp3Log("FAILURE", "Power 2 TCP listener error", {
    error: error.message,
    port: LBP3_TCP_PORT
  });
});

function lbp3CleanupSecurity() {
  const now = Date.now();

  for (const [nonce, record] of lbp3Power.security.usedNonces.entries()) {
    if (record.expiresAt <= now) {
      lbp3Power.security.usedNonces.delete(nonce);
    }
  }

  for (const [ip, record] of lbp3Power.security.rate.entries()) {
    if (now - record.startedAt > LBP3_RATE_WINDOW_MS) {
      lbp3Power.security.rate.delete(ip);
    }
  }
}

function lbp3ScheduleRetry(kind) {
  const key = kind === "tcp" ? "tcpTimer" : "serviceTimer";
  const attemptKey = kind === "tcp" ? "tcpAttempt" : "serviceAttempt";

  if (lbp3Power.retry[key]) return;

  const attempt = lbp3Power.retry[attemptKey];
  const delay = Math.min(
    LBP3_RETRY_MAX_MS,
    LBP3_RETRY_BASE_MS * Math.pow(2, Math.min(attempt, 5))
  );

  lbp3Power.retry[attemptKey]++;
  lbp3Power.retryCount++;

  lbp3Log("RETRY", `Power 2 ${kind} retry scheduled`, {
    attempt: lbp3Power.retry[attemptKey],
    delayMs: delay
  });

  lbp3Power.retry[key] = setTimeout(() => {
    lbp3Power.retry[key] = null;
    lbp3Start(kind);
  }, delay);
}

function lbp3Start(kind) {
  if (kind === "tcp") {
    if (lbp3Power.online) return;

    try {
      lbp3TcpServer.listen(LBP3_TCP_PORT, "0.0.0.0", () => {
        lbp3Power.online = true;
        lbp3Power.retry.tcpAttempt = 0;
        lbp3Log("STARTUP", "Power 2 LBP3 TCP transport online", {
          ip: SERVER_IP,
          port: LBP3_TCP_PORT
        });
      });
    } catch (error) {
      lbp3Power.failureCount++;
      lbp3ScheduleRetry("tcp");
    }

    return;
  }

  if (lbp3Power.serviceOnline) return;

  try {
    lbp3ServiceServer.listen(LBP3_SERVICE_PORT, "0.0.0.0", () => {
      lbp3Power.serviceOnline = true;
      lbp3Power.retry.serviceAttempt = 0;
      lbp3Log("STARTUP", "Power 2 LBP3 service API online", {
        ip: SERVER_IP,
        port: LBP3_SERVICE_PORT
      });
    });
  } catch (error) {
    lbp3Power.failureCount++;
    lbp3ScheduleRetry("service");
  }
}

setInterval(lbp3CleanupSecurity, 30 * 1000);

/* ------------------------------------------------------------------ */
/* POWER 2 startup                                                     */
/* ------------------------------------------------------------------ */

if (ENABLE_LBP3_TCP) lbp3Start("tcp");
if (ENABLE_LBP3_SERVICE) lbp3Start("service");

/* ------------------------------------------------------------------ */
/* DNS upstream health checking                                        */
/* ------------------------------------------------------------------ */

let fastestDnsUpstream =
  DNS_UPSTREAMS[0];

function probeDnsUpstream(host) {
  return new Promise(resolve => {
    const socket =
      dgram.createSocket("udp4");

    const start =
      Date.now();

    let finished = false;

    const finish = result => {
      if (finished) return;

      finished = true;

      try {
        socket.close();
      } catch (_) {}

      resolve(result);
    };

    socket.once(
      "message",
      () => {
        finish({
          host,
          ms: Date.now() - start
        });
      }
    );

    socket.once(
      "error",
      () => {
        finish(null);
      }
    );

    const query =
      Buffer.from([
        0x12, 0x34,
        0x01, 0x00,
        0x00, 0x01,
        0x00, 0x00,
        0x00, 0x00,
        0x00, 0x00,

        0x03, 0x77, 0x77, 0x77,
        0x06, 0x67, 0x6f, 0x6f,
        0x67, 0x6c, 0x65,
        0x03, 0x63, 0x6f, 0x6d,
        0x00,

        0x00, 0x01,
        0x00, 0x01
      ]);

    socket.send(
      query,
      53,
      host,
      error => {
        if (error) {
          finish(null);
        }
      }
    );

    setTimeout(() => {
      finish(null);
    }, 1500);
  });
}

async function updateFastestDns() {
  const results = [];

  for (
    const upstream
    of DNS_UPSTREAMS
  ) {
    const result =
      await probeDnsUpstream(
        upstream
      );

    if (result) {
      results.push(result);
    }
  }

  if (!results.length) {
    return;
  }

  results.sort(
    (a, b) =>
      a.ms - b.ms
  );

  fastestDnsUpstream =
    results[0].host;

  logEvent(
    "dns_health",
    `Fastest DNS upstream: ${fastestDnsUpstream}`,
    {
      latency:
        results[0].ms
    }
  );
}

setInterval(
  updateFastestDns,
  45 * 1000
);

/* ------------------------------------------------------------------ */
/* Maintenance                                                         */
/* ------------------------------------------------------------------ */

function cleanupSessions() {
  const timestamp =
    Date.now();

  db.sessions =
    db.sessions.filter(
      session =>
        Number(
          session.expiresAt
        ) > timestamp
    );
}

function cleanupRandomQueue() {
  for (
    const [
      group,
      userId
    ]
    of activeRandomQueue.entries()
  ) {
    const user =
      getUserById(userId);

    if (
      !user ||
      user.deleted ||
      user.banned ||
      user.ageGroup !== group
    ) {
      activeRandomQueue.delete(
        group
      );
    }
  }
}

function cleanupRandomChats() {
  const timestamp =
    Date.now();

  for (
    const [
      chatId,
      chat
    ]
    of randomChats.entries()
  ) {
    if (
      chat.deletedUserId &&
      chat.deleteDeadline &&
      timestamp >=
        chat.deleteDeadline
    ) {
      endRandomChat(
        chatId,
        "account_deleted"
      );

      continue;
    }

    if (
      timestamp -
        Date.parse(
          chat.updatedAt
        ) >
      RANDOM_MATCH_TIMEOUT_MS
    ) {
      endRandomChat(
        chatId,
        "timeout"
      );
    }
  }
}

function maintenance() {
  cleanupSessions();
  cleanupPresence();
  cleanupRandomQueue();
  cleanupRandomChats();

  saveSoon();
}

setInterval(
  maintenance,
  30 * 1000
);

/* ------------------------------------------------------------------ */
/* Monitoring                                                          */
/* ------------------------------------------------------------------ */

setInterval(() => {
  const realPlayers =
    db.users.filter(
      user =>
        !user.deleted &&
        !user.banned &&
        isUserOnline(user.id)
    ).length;

  logEvent(
    "monitor",
    `LinkUp online: ${realPlayers}`,
    {
      realPlayers,
      queuedRandomUsers:
        activeRandomQueue.size,
      randomChats:
        randomChats.size,
      users:
        db.users.filter(
          user => !user.deleted
        ).length
    }
  );
}, 10 * 1000);

/* ------------------------------------------------------------------ */
/* Startup                                                             */
/* ------------------------------------------------------------------ */

httpServer.listen(
  HTTP_PORT,
  "0.0.0.0",
  () => {
    logEvent(
      "startup",
      `${SERVER_NAME} HTTP server started`,
      {
        port: HTTP_PORT,
        website:
          "GotACrush.html",
        database:
          path.basename(DB_FILE)
      }
    );

    console.log("");
    console.log("====================================");
    console.log("            LINKUP SERVER");
    console.log("====================================");
    console.log(
      `Website: ${process.env.RENDER_EXTERNAL_URL || `http://${SERVER_IP}:${HTTP_PORT}`}/`
    );
    console.log(
      `HTTP:    0.0.0.0:${HTTP_PORT}`
    );
    console.log(
      `DNS:     0.0.0.0:${DNS_PORT}`
    );
    console.log(
      `LBP3:    POWER 2 TCP 0.0.0.0:${LBP3_TCP_PORT}`
    );
    console.log(
      `LBP3 API: POWER 2 HTTP 0.0.0.0:${LBP3_SERVICE_PORT}`
    );
    console.log(
      `Database: ${path.basename(DB_FILE)}`
    );
    console.log(
      `HTML:    ${path.basename(HTML_FILE)}`
    );
    console.log(
      "Random chat: TEXT ONLY"
    );
    console.log(
      "===================================="
    );
    console.log("");
  }
);

if (ENABLE_DNS) {
  dnsServer.bind(
    DNS_PORT,
    "0.0.0.0",
    () => {
      logEvent(
        "startup",
        `${SERVER_NAME} DNS server started`,
        {
          port: DNS_PORT,
          ip: SERVER_IP
        }
      );

      console.log(
        `DNS server listening on UDP ${DNS_PORT}`
      );
    }
  );
} else {
  console.log("DNS listener disabled (required for Render web services).");
}

/* ------------------------------------------------------------------ */
/* Process handling                                                    */
/* ------------------------------------------------------------------ */

function shutdown(signal) {
  console.log(
    `\n${signal} received. Shutting down...`
  );

  try {
    saveDatabase();
  } catch (_) {}

  try {
    httpServer.close();
  } catch (_) {}

  try {
    dnsServer.close();
  } catch (_) {}

  try {
    lbp3TcpServer.close();
  } catch (_) {}

  try {
    lbp3ServiceServer.close();
  } catch (_) {}

  if (lbp3Power.retry.tcpTimer) {
    clearTimeout(lbp3Power.retry.tcpTimer);
  }

  if (lbp3Power.retry.serviceTimer) {
    clearTimeout(lbp3Power.retry.serviceTimer);
  }

  for (
    const timer
    of deletedAccountTimers.values()
  ) {
    clearTimeout(timer);
  }

  deletedAccountTimers.clear();

  process.exit(0);
}

process.on(
  "SIGINT",
  () => shutdown("SIGINT")
);

process.on(
  "SIGTERM",
  () => shutdown("SIGTERM")
);

process.on(
  "uncaughtException",
  error => {
    logEvent(
      "uncaught_exception",
      error.stack ||
        error.message
    );
  }
);

process.on(
  "unhandledRejection",
  error => {
    logEvent(
      "unhandled_rejection",
      String(error)
    );
  }
);

lbp3Log("STARTUP", "Power separation enabled", {
  power1: "DNS / LinkUp accounts",
  power2: "LittleBigPlanet 3",
  sharedIp: SERVER_IP,
  dnsDoesNotCallLbp3: true,
  lbp3HasIndependentState: true
});

logEvent(
  "startup",
  `${SERVER_NAME} ${SERVER_FILE} loaded`,
  {
    node: process.version,
    platform: os.platform(),
    pid: process.pid,
    database:
      path.basename(DB_FILE)
  }
);
