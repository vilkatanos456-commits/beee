#!/usr/bin/env python3
"""
Telegram-бот: ищет СВОБОДНЫЕ редкие ники Roblox.  Управление кнопками и командами.

Установка:  pip install pyTelegramBotAPI requests redis
            (redis нужен только если хочешь хранить прогресс на хостинге)

Настройки (в блоке ниже ИЛИ переменными окружения):
  TG_BOT_TOKEN  токен от @BotFather
  TG_CHAT_ID    твой chat id (можно несколько через запятую).
                Пока не задан — бот в режиме настройки: пришлёт тебе твой id
  REDIS_URL     (необязательно) адрес Redis, чтобы прогресс переживал перезапуски
                на бесплатном Render, например rediss://default:пароль@хост:6379
  CHECK_DELAY   (необязательно) пауза между проверками, сек (по умолчанию 1.5)

Возможности:
  • Кнопки: /menu — все режимы в одно нажатие
  • /all4, /all5     все 4- и 5-буквенные ники (случайный порядок)
  • /pretty 4        «красивые»: aaaa, abab, abba, abcd, qwer ... (3–6 букв)
  • /variants слово  варианты слова: sh4dow, shadow_x, shad_ow, xshadow ...
  • /scan ?#?#       свой шаблон (? = буква, # = цифра), /scan ???? 300 — 300 случайных
  • .txt файл        список слов (по одному в строке)
  • /name a b c      проверить несколько ников (или просто напиши ник в чат)
  • Живая панель прогресса: %, скорость, ETA, найденные; кнопки Стоп / Обновить
  • Умная пауза: при лимитах Roblox (429) бот замедляется, потом сам ускоряется
  • Автопродолжение после перезапуска (файл state.json или Redis)
  • /status /stop /resume /found /export /delay /id
"""

import html
import io
import itertools
import json
import logging
import math
import os
import random
import re
import signal
import string
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import requests
import telebot
from telebot import types

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s", datefmt="%H:%M:%S")
log = logging.getLogger("robloxbot")

# ===== НАСТРОЙКИ =====
TOKEN = ""     # вставь токен от @BotFather ВНУТРИ кавычек (или задай TG_BOT_TOKEN)
ADMIN_ID = 0   # твой chat id (или задай TG_CHAT_ID). Не знаешь — оставь 0 и напиши боту /start
# =====================

TOKEN = TOKEN or os.environ.get("TG_BOT_TOKEN", "")


def _parse_ids(*chunks):
    ids = set()
    for chunk in chunks:
        for part in re.split(r"[,\s;]+", str(chunk or "")):
            if part.lstrip("-").isdigit() and int(part) != 0:
                ids.add(int(part))
    return ids


ADMIN_IDS = _parse_ids(ADMIN_ID, os.environ.get("TG_CHAT_ID", ""))

DELAY = float(os.environ.get("CHECK_DELAY", "1.5"))   # пауза между проверками, сек
MIN_DELAY, MAX_DELAY = 0.3, 30.0
MAX_AUTO_DELAY = 15.0      # потолок автозамедления при лимитах
MAX_ERRORS = 20            # столько ошибок подряд — ставим на паузу
MAX_FULL = 20000           # шаблон больше этого без числа N -> 500 случайных
MAX_WORDS = 5000
MAX_QUICK = 25
PANEL_EVERY = 45           # как часто обновлять панель прогресса, сек
SAVE_EVERY = 30            # как часто сохранять состояние, сек
FOUND_FILE = "found.txt"
CHECKED_FILE = "checked.txt"
STATE_FILE = "state.json"
REDIS_KEY = "robloxbot:state"
ON_RENDER = bool(os.environ.get("RENDER"))
ACCOUNT_URL = "https://www.roblox.com/my/account#!/info"

URL = "https://auth.roblox.com/v1/usernames/validate"
BIRTHDAY = "2000-01-01"
NAME_RE = re.compile(r"^(?=.{3,20}$)(?!_)(?!.*_$)(?!.*_.*_)[A-Za-z0-9_]+$")
LETTERS = string.ascii_lowercase
DIGITS = string.digits

if not TOKEN:
    raise SystemExit("Нет токена: впиши его в TOKEN или задай переменную TG_BOT_TOKEN")

bot = telebot.TeleBot(TOKEN)
ApiError = getattr(getattr(telebot, "apihelper", None), "ApiTelegramException", Exception)

jobs = {}                      # chat_id -> работающая задача (в памяти)
jobs_lock = threading.Lock()
state_lock = threading.RLock()
file_lock = threading.Lock()
SHUTTING_DOWN = threading.Event()


# ============================ хранилище ============================

class Storage:
    """Состояние бота: Redis (если задан REDIS_URL) или локальный файл."""

    def __init__(self):
        self.redis = None
        url = os.environ.get("REDIS_URL", "").strip()
        if url:
            try:
                import redis  # pip install redis
                self.redis = redis.from_url(url, decode_responses=True, socket_timeout=10)
                self.redis.ping()
                log.info("Хранилище: Redis")
            except Exception as e:  # noqa: BLE001
                log.warning("Redis недоступен (%s) — использую файл %s", e, STATE_FILE)
                self.redis = None

    @property
    def durable(self):
        """Переживёт ли состояние перезапуск (на бесплатном Render без Redis — нет)."""
        return self.redis is not None or not ON_RENDER

    def load(self):
        data = {}
        try:
            if self.redis is not None:
                raw = self.redis.get(REDIS_KEY)
            else:
                with open(STATE_FILE, encoding="utf-8") as f:
                    raw = f.read()
            data = json.loads(raw) if raw else {}
        except FileNotFoundError:
            pass
        except Exception as e:  # noqa: BLE001
            log.warning("Не удалось прочитать состояние: %s", e)
        return data if isinstance(data, dict) else {}

    def save(self, text):
        try:
            if self.redis is not None:
                self.redis.set(REDIS_KEY, text)
            else:
                tmp = STATE_FILE + ".tmp"
                with open(tmp, "w", encoding="utf-8") as f:
                    f.write(text)
                os.replace(tmp, STATE_FILE)
        except Exception as e:  # noqa: BLE001
            log.warning("Не удалось сохранить состояние: %s", e)


storage = Storage()
state = storage.load()
state.setdefault("jobs", {})      # chat_id(str) -> описание задачи
state.setdefault("found", [])     # все найденные свободные ники
try:
    DELAY = min(max(float(state.get("delay", DELAY)), MIN_DELAY), MAX_DELAY)
except (TypeError, ValueError):
    pass
_last_save = 0.0


def persist(force=False):
    global _last_save
    now = time.time()
    with state_lock:
        if not force and now - _last_save < SAVE_EVERY:
            return
        state["delay"] = DELAY
        text = json.dumps(state, ensure_ascii=False)
        _last_save = now
    storage.save(text)


def load_checked():
    try:
        with open(CHECKED_FILE, encoding="utf-8") as f:
            return {line.strip() for line in f if line.strip()}
    except FileNotFoundError:
        return set()


checked = load_checked()


def append_line(path, line):
    with file_lock:
        try:
            with open(path, "a", encoding="utf-8") as f:
                f.write(line + "\n")
        except OSError as e:
            log.warning("Не удалось записать %s: %s", path, e)


# ============================ ники ============================

def valid_format(name):
    return bool(NAME_RE.match(name)) and not name.isdigit()


def pattern_options(pattern):
    opts = []
    for ch in pattern:
        if ch == "?":
            opts.append(LETTERS)
        elif ch == "#":
            opts.append(DIGITS)
        else:
            opts.append(ch)
    return opts


def gen_pattern(opts, n, seed):
    rng = random.Random(seed)
    if n:
        seen = set()
        tries = 0
        while len(seen) < n and tries < n * 20:
            tries += 1
            name = "".join(rng.choice(o) for o in opts)
            if name not in seen:
                seen.add(name)
                yield name
        return
    names = ["".join(p) for p in itertools.product(*opts)]
    rng.shuffle(names)
    yield from names


def gen_all(length, start_i=0):
    """Все комбинации из `length` букв в псевдослучайном, но ВСЕГДА одинаковом порядке:
    поэтому прогресс хранится одним числом. Список в памяти не строится."""
    total = 26 ** length
    rng = random.Random(1000003 * length + 7)
    step = rng.randrange(total // 3, total)
    while math.gcd(step, total) != 1:
        step += 1
    start = rng.randrange(total)
    for i in range(start_i, total):
        x = (start + i * step) % total
        chars = []
        for _ in range(length):
            x, r = divmod(x, 26)
            chars.append(LETTERS[r])
        yield "".join(reversed(chars))


KEY_ROWS = ["qwertyuiop", "asdfghjkl", "zxcvbnm"]


def _runs(sequences, n):
    out = []
    for s in sequences:
        for i in range(len(s) - n + 1):
            piece = s[i:i + n]
            out.append(piece)
            out.append(piece[::-1])
    return out


def pretty_names(n):
    """«Красивые» ники: ряды букв, клавиатурные ряды, повторы и палиндромы."""
    names = _runs([LETTERS], n) + _runs(KEY_ROWS, n)
    shapes = ["a" + "".join("b" if (bits >> k) & 1 else "a" for k in range(n - 1))
              for bits in range(2 ** (n - 1))]
    for shape in sorted(shapes, key=lambda s: (len(set(s)) > 1, s != s[::-1], s)):
        if "b" not in shape:
            names += [c * n for c in LETTERS]
            continue
        for x in LETTERS:
            for y in LETTERS:
                if x != y:
                    names.append("".join(x if ch == "a" else y for ch in shape))
    return [x for x in dict.fromkeys(names) if valid_format(x)]


LEET = {"a": "4", "e": "3", "i": "1", "o": "0", "s": "5", "t": "7", "b": "8", "g": "9", "l": "1"}
PREFIXES = ["x", "xx", "xo", "mr", "its", "im", "the", "real", "pro", "my", "ur", "i"]
SUFFIXES = ["x", "xx", "xd", "hd", "gg", "tv", "yt", "pro", "official", "rbx", "rblx",
            "zz", "007", "123", "_x", "_gg"]


def variant_names(word):
    """Варианты слова: без/с перестановкой букв, leet, подчёркивание, приставки, цифры."""
    w = word.lower()
    out = [w]
    out += [w[:i] + w[i + 1:] for i in range(len(w))]
    out += [w[:i] + w[i + 1] + w[i] + w[i + 2:] for i in range(len(w) - 1)]
    out += [w[:i] + LEET[ch] + w[i + 1:] for i, ch in enumerate(w) if ch in LEET]
    out.append("".join(LEET.get(ch, ch) for ch in w))
    out += [w[:i] + "_" + w[i:] for i in range(1, len(w))]
    out.append("".join(ch for ch in w if ch not in "aeiou"))
    out += [w[:i + 1] + w[i] + w[i + 1:] for i in range(len(w))]
    out.append(w[::-1])
    out += [p + w for p in PREFIXES]
    out += [w + s for s in SUFFIXES]
    out += [w + str(d) for d in range(10)]
    out += [w + f"{d:02d}" for d in range(10, 100)]
    return [x for x in dict.fromkeys(out) if valid_format(x)][:3000]


def make_names(spec):
    """Итератор имён для задачи, уже встроенный на её сохранённую позицию."""
    kind, pos = spec["kind"], spec.get("pos", 0)
    if kind == "all":
        return gen_all(spec["length"], pos)
    if kind == "scan":
        return itertools.islice(
            gen_pattern(pattern_options(spec["pattern"]), spec["n"], spec["seed"]), pos, None)
    if kind == "pretty":
        return iter(pretty_names(spec["length"])[pos:])
    if kind == "variants":
        return iter(variant_names(spec["word"])[pos:])
    if kind == "words":
        return iter(spec["words"][pos:])
    raise ValueError(f"неизвестный тип задачи: {kind}")


# ============================ форматирование ============================

def num(n):
    return f"{int(n):,}".replace(",", " ")


def bar(frac, width=12):
    k = int(round(min(max(frac, 0.0), 1.0) * width))
    return "█" * k + "░" * (width - k)


def fmt_duration(seconds):
    seconds = max(seconds, 0)
    if seconds < 90:
        return "меньше 2 мин"
    if seconds < 2 * 3600:
        return f"~{seconds / 60:.0f} мин"
    if seconds < 48 * 3600:
        return f"~{seconds / 3600:.0f} ч"
    return f"~{seconds / 86400:.0f} дн."


# ============================ Roblox ============================

def check(session, name, stop, info=None):
    """'free' | 'taken' | 'blocked' | 'error' | 'stopped'.
    В info копятся счётчик лимитов (429) и последняя HTTP-ошибка."""
    info = info if info is not None else {}
    backoff = 5
    for _ in range(6):
        if stop.is_set():
            return "stopped"
        try:
            r = session.get(
                URL,
                params={"Username": name, "Birthday": BIRTHDAY, "Context": "Signup"},
                timeout=15,
            )
        except requests.RequestException:
            info["last_http"] = "нет связи"
            stop.wait(backoff)
            backoff = min(backoff * 2, 120)
            continue

        if r.status_code == 429:
            info["limited"] = info.get("limited", 0) + 1
            try:
                wait = int(r.headers.get("Retry-After", backoff))
            except (TypeError, ValueError):
                wait = backoff
            stop.wait(min(max(wait, 1), 300))
            backoff = min(backoff * 2, 300)
            continue

        if r.status_code != 200:
            info["last_http"] = f"HTTP {r.status_code}"
            return "error"
        try:
            code = r.json().get("code")
        except ValueError:
            info["last_http"] = "странный ответ"
            return "error"
        if code == 0:
            return "free"
        if code == 1:
            return "taken"
        return "blocked"      # 2 = запрещённое слово, 10 = похоже на личные данные и т.д.
    return "error"


# ============================ Telegram: помощники ============================

def tg(fn, *args, **kwargs):
    """Вызов Telegram API: повтор при лимите 429, ошибки не роняют бота."""
    for _ in range(3):
        try:
            return fn(*args, **kwargs)
        except ApiError as e:
            if "message is not modified" in str(e):
                return None
            if getattr(e, "error_code", None) == 429:
                params = (getattr(e, "result_json", None) or {}).get("parameters", {})
                time.sleep(min(int(params.get("retry_after", 5)) + 1, 60))
                continue
            log.warning("Telegram API: %s", e)
            return None
        except Exception as e:  # noqa: BLE001
            log.warning("Telegram: %s", e)
            return None
    return None


def say(chat_id, text, markup=None, silent=False):
    return tg(bot.send_message, chat_id, text, parse_mode="HTML",
              reply_markup=markup, disable_notification=silent)


def button(text, data=None, url=None):
    return types.InlineKeyboardButton(text=text, callback_data=data, url=url)


def main_menu():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("🔍 Все 4 буквы", "m:all4"), button("🔍 Все 5 букв", "m:all5"))
    kb.row(button("✨ Красивые 4", "m:pr4"), button("✨ Красивые 5", "m:pr5"))
    kb.row(button("📊 Статус", "m:status"), button("⏹ Стоп", "stop"), button("▶️ Продолжить", "m:resume"))
    kb.row(button("📋 Найденные", "m:found"), button("📤 Экспорт", "m:export"), button("⚙️ Пауза", "m:set"))
    return kb


def panel_markup():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("⏹ Стоп", "stop"), button("🔄 Обновить", "refresh"))
    return kb


def settings_text():
    return (f"⚙️ Пауза между проверками: <b>{DELAY:.1f} с</b>\n"
            "Меньше — быстрее, но Roblox чаще отвечает «слишком много запросов». "
            "Бот сам замедляется при лимитах и потом возвращается к этой паузе.")


def settings_markup():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("➖ 0.5 с", "dl:-"), button("➕ 0.5 с", "dl:+"))
    return kb


# ============================ задачи ============================

def new_spec(kind, title, total, **extra):
    spec = {"kind": kind, "title": title, "total": total, "pos": 0, "running": True,
            "stats": {"checked": 0, "free": 0, "limited": 0}, "created": time.time()}
    spec.update(extra)
    return spec


def new_job(spec):
    return {"stop": threading.Event(), "spec": spec, "t0": time.time(), "pos0": spec["pos"],
            "current": "", "delay": DELAY, "ok_streak": 0, "errors": 0,
            "limited": 0, "last_http": None, "panel": None, "thread": None}


class Panel:
    """Одно сообщение с живым прогрессом: редактируется, а не спамит чат."""

    def __init__(self, chat_id, job):
        self.chat_id, self.job = chat_id, job
        self.msg_id = None
        self.last = 0.0

    def text(self, status=None):
        job = self.job
        spec = job["spec"]
        st = spec["stats"]
        total = max(spec.get("total", 0), 1)
        pos = min(spec["pos"], total)
        frac = pos / total
        elapsed = max(time.time() - job["t0"], 1.0)
        moved = pos - job["pos0"]
        rate = moved / elapsed if (elapsed > 60 and moved >= 10) else 1 / (job["delay"] + 0.45)
        eta = (total - pos) / rate if rate > 0 else 0
        head = {None: "⏳", "done": "🏁", "stopped": "⏸", "blocked": "⚠️", "crashed": "💥"}[status]
        lines = [
            f"{head} <b>{html.escape(spec['title'])}</b>",
            f"{bar(frac)} {frac * 100:.1f}%  ({num(pos)} из {num(total)})",
            f"🟢 Найдено свободных: <b>{st['free']}</b>   ·   проверено: {num(st['checked'])}",
        ]
        if status is None:
            lines.append(f"⚡ ~{rate * 60:.0f} ников/мин · пауза {job['delay']:.1f} с")
            lines.append(f"🕒 Осталось: {fmt_duration(eta)}")
        if st["limited"]:
            lines.append(f"🚦 Лимитов Roblox (429): {st['limited']} — бот сам подстраивает паузу")
        if status is None and not storage.durable and spec["kind"] == "all":
            lines.append(f"📍 Позиция: {pos} (нужна для /all{spec['length']} {pos} после перезапуска)")
        return "\n".join(lines)

    def send(self):
        m = say(self.chat_id, self.text(), panel_markup(), silent=True)
        self.msg_id = getattr(m, "message_id", None)
        self.last = time.time()

    def update(self, force=False, status=None):
        now = time.time()
        if self.msg_id is None or (not force and now - self.last < PANEL_EVERY):
            return
        self.last = now
        kwargs = {"parse_mode": "HTML"}
        if status is None:
            kwargs["reply_markup"] = panel_markup()
        tg(bot.edit_message_text, self.text(status), chat_id=self.chat_id,
           message_id=self.msg_id, **kwargs)


def register_found(name):
    with state_lock:
        if name not in state["found"]:
            state["found"].append(name)
    append_line(FOUND_FILE, name)
    persist(force=True)


def announce(chat_id, name):
    kb = types.InlineKeyboardMarkup()
    kb.row(button("🔄 Перепроверить", f"re:{name}"), button("✏️ Занять на Roblox", url=ACCOUNT_URL))
    say(chat_id, f"🟢 Свободен ник: <code>{name}</code>", kb)


def run_job(chat_id, job):
    spec = job["spec"]
    stats = spec["stats"]
    track = spec["kind"] != "all"          # для «все N букв» хватает позиции
    session = requests.Session()
    session.headers["User-Agent"] = "Mozilla/5.0 (username-checker)"
    panel = Panel(chat_id, job)
    job["panel"] = panel
    panel.send()
    persist(force=True)

    base = spec["pos"]
    idx = -1
    outcome = "done"
    try:
        for idx, name in enumerate(make_names(spec)):
            spec["pos"] = base + idx
            if job["stop"].is_set():
                outcome = "stopped"
                break
            name = name.strip().lower()
            if not valid_format(name) or (track and name in checked):
                continue

            job["current"] = name
            limited_before = job["limited"]
            status = check(session, name, job["stop"], job)
            if status == "stopped":
                outcome = "stopped"
                break
            if status == "error":
                job["errors"] += 1
                if job["errors"] >= MAX_ERRORS:
                    outcome = "blocked"
                    break
                job["stop"].wait(job["delay"] * 2)
                continue
            job["errors"] = 0

            if status == "free":                       # подтверждаем вторым запросом
                job["stop"].wait(0.7)
                again = check(session, name, job["stop"], job)
                if again == "stopped":
                    outcome = "stopped"
                    break
                if again in ("taken", "blocked"):
                    status = again

            stats["checked"] += 1
            if track:
                checked.add(name)
                append_line(CHECKED_FILE, name)
            if status == "free":
                stats["free"] += 1
                register_found(name)
                announce(chat_id, name)

            hits = job["limited"] - limited_before     # умная пауза
            if hits:
                stats["limited"] += hits
                job["delay"] = min(job["delay"] * 1.5 + 0.2, MAX_AUTO_DELAY)
                job["ok_streak"] = 0
            else:
                job["ok_streak"] += 1
                if job["ok_streak"] >= 40:
                    job["ok_streak"] = 0
                    job["delay"] = max(DELAY, job["delay"] * 0.9)
            job["delay"] = max(job["delay"], min(DELAY, MAX_AUTO_DELAY))

            if (spec["kind"] == "all" and not storage.durable
                    and stats["checked"] % 2000 == 0):
                say(chat_id, f"📍 Позиция {spec['pos']}. Если бот перезапустится, продолжи: "
                             f"<code>/all{spec['length']} {spec['pos']}</code>", silent=True)
            panel.update()
            persist()
            job["stop"].wait(job["delay"] + random.uniform(0, 0.4))
        else:
            spec["pos"] = base + idx + 1
    except Exception:  # noqa: BLE001
        log.exception("Сбой в задаче")
        outcome = "crashed"
    finally:
        with jobs_lock:
            jobs.pop(chat_id, None)
        if SHUTTING_DOWN.is_set():
            spec["running"] = True           # после перезапуска продолжится само
            persist(force=True)
        else:
            _finish_job(chat_id, job, outcome)


def _finish_job(chat_id, job, outcome):
    spec, stats = job["spec"], job["spec"]["stats"]
    if outcome == "done":
        with state_lock:
            state["jobs"].pop(str(chat_id), None)
    else:
        spec["running"] = False              # пауза: /resume продолжит с этой позиции
    persist(force=True)
    job["panel"].update(force=True, status=outcome)
    tail = f"Проверено: {num(stats['checked'])}, свободных: {stats['free']}."
    if outcome == "done":
        text = f"🏁 Готово: {html.escape(spec['title'])}. {tail}\nВсе найденные: /found"
    elif outcome == "stopped":
        text = (f"⏹ Остановлено на позиции {num(spec['pos'])} из {num(spec['total'])}. {tail}\n"
                "Продолжить с этого места: /resume")
    elif outcome == "blocked":
        text = (f"⚠️ {MAX_ERRORS} ошибок подряд ({job['last_http'] or 'нет ответа'}): Roblox не отвечает "
                f"или блокирует запросы с этого сервера. Поставил на паузу. {tail}\n"
                "Попробуй позже: /resume")
    else:
        text = f"💥 Внутренняя ошибка, задача на паузе. {tail}\nПопробуй /resume"
    say(chat_id, text)


def begin(chat_id, spec):
    with jobs_lock:
        busy = chat_id in jobs
        if not busy:
            job = new_job(spec)
            jobs[chat_id] = job
    if busy:
        say(chat_id, "Уже идёт проверка. Смотри /status или останови /stop")
        return False
    spec["running"] = True
    with state_lock:
        state["jobs"][str(chat_id)] = spec
    job["thread"] = threading.Thread(target=run_job, args=(chat_id, job), daemon=True)
    job["thread"].start()
    return True


def start_all(chat_id, length, pos=0):
    full = 26 ** length
    spec = new_spec("all", f"Все {length}-буквенные ники", full, length=length)
    spec["pos"] = min(max(pos, 0), full)
    return begin(chat_id, spec)


def start_pretty(chat_id, n):
    names = pretty_names(n)
    return begin(chat_id, new_spec(
        "pretty", f"Красивые {n}-буквенные (повторы, палиндромы, ряды)", len(names), length=n))


def resume_job(chat_id):
    spec = state["jobs"].get(str(chat_id))
    if chat_id in jobs:
        say(chat_id, "Проверка уже идёт: /status")
    elif not spec:
        say(chat_id, "Нечего продолжать — нет приостановленных задач.")
    else:
        say(chat_id, f"▶️ Продолжаю: <b>{html.escape(spec['title'])}</b> с позиции {num(spec['pos'])}")
        begin(chat_id, spec)


def resume_saved_jobs():
    """После перезапуска продолжаем задачи, которые работали до него."""
    for cid, spec in list(state["jobs"].items()):
        if spec.get("running") and int(cid) not in jobs:
            say(int(cid), f"♻️ Бот перезапущен — продолжаю: <b>{html.escape(spec['title'])}</b> "
                          f"с позиции {num(spec['pos'])}")
            begin(int(cid), spec)


def send_status(chat_id):
    job = jobs.get(chat_id)
    spec = state["jobs"].get(str(chat_id))
    if job:
        say(chat_id, job["panel"].text() + f"\nСейчас: <code>{job['current']}</code>")
    elif spec:
        say(chat_id, f"⏸ На паузе: <b>{html.escape(spec['title'])}</b>\n"
                     f"Позиция {num(spec['pos'])} из {num(spec['total'])}, "
                     f"найдено свободных: {spec['stats']['free']}\nПродолжить: /resume")
    else:
        say(chat_id, "Сейчас ничего не запущено. Открой /menu")
    if not storage.durable:
        say(chat_id, "⚠️ Прогресс не сохраняется при перезапуске (бесплатный Render без Redis). "
                     "Подключи REDIS_URL — тогда бот будет продолжать сам.", silent=True)


def stop_job(chat_id):
    job = jobs.get(chat_id)
    if not job:
        return False
    job["stop"].set()
    return True


# ============================ обработчики ============================

def allowed(chat_id):
    return bool(ADMIN_IDS) and chat_id in ADMIN_IDS


def guard(m):
    log.info("[вход] chat_id=%s text=%r", m.chat.id, getattr(m, "text", None))
    if allowed(m.chat.id):
        return True
    if not ADMIN_IDS:
        tg(bot.reply_to, m,
           f"🔧 Первый запуск. Твой chat id: <code>{m.chat.id}</code>\n"
           "Впиши его в TG_CHAT_ID (переменная окружения) или в ADMIN_ID в коде и "
           "перезапусти бота — после этого он будет слушаться только тебя.",
           parse_mode="HTML")
    else:
        tg(bot.reply_to, m, f"⛔ Доступ закрыт. Твой chat id: <code>{m.chat.id}</code>. "
                            "Если это ты — добавь его в TG_CHAT_ID.", parse_mode="HTML")
    return False


HELP = (
    "<b>Ищу свободные ники Roblox</b>\n\n"
    "/menu — все режимы кнопками\n"
    "<code>/all4</code> · <code>/all5</code> — ВСЕ 4- и 5-буквенные (продолжить с места: <code>/all4 12345</code>)\n"
    "<code>/pretty 4</code> — «красивые»: aaaa, abab, abba, abcd, qwer… (3–6 букв)\n"
    "<code>/variants shadow</code> — варианты слова: sh4dow, shad_ow, xshadow…\n"
    "<code>/scan ?#?#</code> — свой шаблон (? буква, # цифра); <code>/scan ???? 300</code> — 300 случайных\n"
    "Отправь .txt со словами — проверю их\n"
    "<code>/name a b c</code> или просто напиши ник — быстрая проверка\n\n"
    "/status · /stop · /resume — управление\n"
    "/found · /export — найденные ники\n"
    "<code>/delay 1.5</code> — пауза между проверками\n\n"
    "Свободный ник нельзя забронировать — занимай сразу, смена ника на Roblox стоит 1000 Robux."
)


@bot.message_handler(commands=["id"])
def cmd_id(m):
    tg(bot.reply_to, m, f"Твой chat id: <code>{m.chat.id}</code>", parse_mode="HTML")


@bot.message_handler(commands=["start", "menu"])
def cmd_start(m):
    if not guard(m):
        return
    say(m.chat.id, "🤖 <b>Ищу свободные ники Roblox.</b> Выбери действие:\n"
                   "(все команды: /help)", main_menu())


@bot.message_handler(commands=["help"])
def cmd_help(m):
    if guard(m):
        say(m.chat.id, HELP)


@bot.message_handler(commands=["all4", "all5"])
def cmd_all(m):
    if not guard(m):
        return
    length = 4 if m.text.startswith("/all4") else 5
    parts = m.text.split()
    pos = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0
    start_all(m.chat.id, length, pos)


@bot.message_handler(commands=["pretty"])
def cmd_pretty(m):
    if not guard(m):
        return
    parts = m.text.split()
    n = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 4
    if not 3 <= n <= 6:
        tg(bot.reply_to, m, "Длина от 3 до 6, например: /pretty 4")
        return
    start_pretty(m.chat.id, n)


@bot.message_handler(commands=["variants"])
def cmd_variants(m):
    if not guard(m):
        return
    parts = m.text.split()
    if len(parts) < 2 or not re.fullmatch(r"[A-Za-z0-9]{2,16}", parts[1]):
        tg(bot.reply_to, m, "Пример: /variants shadow  (слово 2–16 символов, латиница/цифры)")
        return
    word = parts[1].lower()
    names = variant_names(word)
    begin(m.chat.id, new_spec("variants", f"Варианты слова «{word}»", len(names), word=word))


@bot.message_handler(commands=["scan"])
def cmd_scan(m):
    if not guard(m):
        return
    args = m.text.split()[1:]
    if not args:
        tg(bot.reply_to, m, "Пример: /scan ???? 300  (? = буква, # = цифра)")
        return
    pattern = args[0].lower()
    if not re.fullmatch(r"[?#a-z0-9_]{3,20}", pattern):
        tg(bot.reply_to, m, "Шаблон: 3–20 символов, можно ? # буквы цифры _")
        return
    n = int(args[1]) if len(args) > 1 and args[1].isdigit() else 0
    full = math.prod(len(o) for o in pattern_options(pattern))
    note = ""
    if n >= full:
        n = 0
    if not n and full > MAX_FULL:
        n = 500
        note = f" — вариантов {num(full)}, беру {n} случайных"
    total = n or full
    title = f"Шаблон {pattern}" + (f", {n} случайных" if n else "")
    if note:
        say(m.chat.id, f"ℹ️ Шаблон <code>{pattern}</code>{note}")
    begin(m.chat.id, new_spec("scan", title, total, pattern=pattern, n=n,
                              seed=random.randrange(2 ** 31)))


@bot.message_handler(content_types=["document"])
def on_document(m):
    if not guard(m):
        return
    doc = m.document
    if not (doc.file_name or "").lower().endswith(".txt"):
        tg(bot.reply_to, m, "Нужен .txt файл: один ник в строке")
        return
    if doc.file_size and doc.file_size > 1_000_000:
        tg(bot.reply_to, m, "Файл слишком большой (макс. 1 МБ)")
        return
    data = tg(lambda: bot.download_file(bot.get_file(doc.file_id).file_path))
    if data is None:
        tg(bot.reply_to, m, "Не получилось скачать файл, попробуй ещё раз")
        return
    lines = data.decode("utf-8", "ignore").splitlines()
    names = list(dict.fromkeys(x.strip().lower() for x in lines if x.strip()))[:MAX_WORDS]
    if not names:
        tg(bot.reply_to, m, "В файле нет ников")
        return
    begin(m.chat.id, new_spec("words", f"Слова из файла {doc.file_name}", len(names), words=names))


def quick_check(chat_id, names):
    session = requests.Session()
    session.headers["User-Agent"] = "Mozilla/5.0 (username-checker)"
    never = threading.Event()
    lines = []
    for name in names:
        if not valid_format(name):
            lines.append(f"⚪ <code>{html.escape(name)}</code> — Roblox не принимает такой формат")
            continue
        st = check(session, name, never)
        lines.append({
            "free": f"🟢 <code>{name}</code> — свободен",
            "taken": f"🔴 <code>{name}</code> — занят",
            "blocked": f"⛔ <code>{name}</code> — запрещён Roblox",
        }.get(st, f"⚠️ <code>{name}</code> — не удалось проверить"))
        time.sleep(0.4)
    say(chat_id, "\n".join(lines))


def start_quick(chat_id, names):
    names = list(dict.fromkeys(n.lower() for n in names if n))
    if not names:
        say(chat_id, "Напиши ник, например: /name abc")
    elif len(names) > MAX_QUICK:
        say(chat_id, f"За раз можно до {MAX_QUICK} ников, для большего используй /scan или .txt")
    else:
        threading.Thread(target=quick_check, args=(chat_id, names), daemon=True).start()


@bot.message_handler(commands=["name"])
def cmd_name(m):
    if guard(m):
        start_quick(m.chat.id, re.split(r"[\s,;]+", m.text)[1:])


@bot.message_handler(commands=["status"])
def cmd_status(m):
    if guard(m):
        send_status(m.chat.id)


@bot.message_handler(commands=["stop"])
def cmd_stop(m):
    if not guard(m):
        return
    if stop_job(m.chat.id):
        tg(bot.reply_to, m, "Останавливаю…")
    else:
        tg(bot.reply_to, m, "Нечего останавливать")


@bot.message_handler(commands=["resume"])
def cmd_resume(m):
    if guard(m):
        resume_job(m.chat.id)


def found_text():
    with state_lock:
        names = list(state["found"])
    if not names:
        return "Пока ничего не найдено"
    shown = names[-50:]
    return (f"Найдено всего: {len(names)} (последние {len(shown)}):\n"
            + "\n".join(f"<code>{x}</code>" for x in shown))


def send_export(chat_id):
    with state_lock:
        names = list(state["found"])
    if not names:
        say(chat_id, "Пока ничего не найдено")
        return
    bio = io.BytesIO("\n".join(names).encode("utf-8"))
    bio.name = "found.txt"
    tg(bot.send_document, chat_id, bio)


@bot.message_handler(commands=["found"])
def cmd_found(m):
    if guard(m):
        say(m.chat.id, found_text())


@bot.message_handler(commands=["export"])
def cmd_export(m):
    if guard(m):
        send_export(m.chat.id)


def set_delay(value):
    global DELAY
    DELAY = round(min(max(value, MIN_DELAY), MAX_DELAY), 2)
    persist(force=True)
    return DELAY


@bot.message_handler(commands=["delay"])
def cmd_delay(m):
    if not guard(m):
        return
    parts = m.text.split()
    if len(parts) < 2:
        say(m.chat.id, settings_text(), settings_markup())
        return
    try:
        value = float(parts[1].replace(",", "."))
    except ValueError:
        tg(bot.reply_to, m, "Нужно число, например: /delay 1")
        return
    set_delay(value)
    say(m.chat.id, settings_text(), settings_markup())


@bot.message_handler(func=lambda m: m.content_type == "text" and not (m.text or "").startswith("/"))
def on_text(m):
    """Обычный текст = быстрая проверка ников."""
    if not guard(m):
        return
    tokens = [t for t in re.split(r"[\s,;]+", m.text.strip()) if t]
    if tokens and all(re.fullmatch(r"[A-Za-z0-9_]+", t) for t in tokens):
        start_quick(m.chat.id, tokens)
    else:
        say(m.chat.id, "Напиши ник латиницей для проверки или открой /menu")


@bot.callback_query_handler(func=lambda c: True)
def on_callback(c):
    chat_id = c.message.chat.id
    if not allowed(chat_id):
        tg(bot.answer_callback_query, c.id, "Нет доступа")
        return
    data = c.data or ""

    if data == "stop":
        ok = stop_job(chat_id)
        tg(bot.answer_callback_query, c.id, "Останавливаю…" if ok else "Нечего останавливать")
    elif data == "refresh":
        job = jobs.get(chat_id)
        if job and job["panel"]:
            job["panel"].update(force=True)
            tg(bot.answer_callback_query, c.id, "Обновлено")
        else:
            tg(bot.answer_callback_query, c.id, "Нет активной проверки")
    elif data.startswith("re:"):
        tg(bot.answer_callback_query, c.id, "Проверяю…")
        start_quick(chat_id, [data[3:]])
    elif data in ("dl:+", "dl:-"):
        set_delay(DELAY + (0.5 if data == "dl:+" else -0.5))
        tg(bot.answer_callback_query, c.id, f"Пауза {DELAY:.1f} с")
        tg(bot.edit_message_text, settings_text(), chat_id=chat_id, message_id=c.message.message_id,
           parse_mode="HTML", reply_markup=settings_markup())
    elif data.startswith("m:"):
        tg(bot.answer_callback_query, c.id)
        action = data[2:]
        if action in ("all4", "all5"):
            start_all(chat_id, int(action[-1]))
        elif action in ("pr4", "pr5"):
            start_pretty(chat_id, int(action[-1]))
        elif action == "status":
            send_status(chat_id)
        elif action == "resume":
            resume_job(chat_id)
        elif action == "found":
            say(chat_id, found_text())
        elif action == "export":
            send_export(chat_id)
        elif action == "set":
            say(chat_id, settings_text(), settings_markup())
    else:
        tg(bot.answer_callback_query, c.id)


# ============================ запуск ============================

class PingHandler(BaseHTTPRequestHandler):
    """Нужен для Render: сервис должен слушать порт и отвечать на пинги."""

    def _ok(self):
        self.send_response(200)
        self.send_header("Content-Type", "text/plain; charset=utf-8")
        self.end_headers()

    def do_GET(self):
        self._ok()
        self.wfile.write(b"ok")

    def do_HEAD(self):
        self._ok()

    def log_message(self, *args):
        pass


def start_ping_server():
    port = os.environ.get("PORT")
    if not port:
        return
    server = ThreadingHTTPServer(("0.0.0.0", int(port)), PingHandler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    log.info("Ping-сервер на порту %s", port)


def shutdown(signum=None, frame=None):
    """Render шлёт SIGTERM при перезапуске: сохраняем прогресс и выходим."""
    if SHUTTING_DOWN.is_set():
        return
    SHUTTING_DOWN.set()
    log.info("Остановка (сигнал %s): сохраняю прогресс…", signum)
    running = list(jobs.values())
    for job in running:
        job["stop"].set()
    for job in running:
        if job.get("thread"):
            job["thread"].join(timeout=8)
    persist(force=True)
    os._exit(0)


def main():
    start_ping_server()
    try:
        me = bot.get_me()
    except Exception as e:  # noqa: BLE001
        raise SystemExit(f"Токен не подошёл или нет интернета: {e}")
    log.info("Бот запущен: @%s | доступ: %s | хранилище: %s", me.username,
             sorted(ADMIN_IDS) or "НЕ ЗАДАН (режим настройки: напиши боту /start)",
             "Redis" if storage.redis else f"файл {STATE_FILE}"
             + ("" if storage.durable else " (на Render сотрётся при перезапуске)"))
    try:
        bot.set_my_commands([telebot.types.BotCommand(c, d) for c, d in [
            ("menu", "меню с кнопками"), ("all4", "все 4-буквенные"), ("all5", "все 5-буквенные"),
            ("pretty", "красивые ники"), ("variants", "варианты слова"), ("scan", "по шаблону"),
            ("name", "проверить ники"), ("status", "прогресс"), ("stop", "остановить"),
            ("resume", "продолжить"), ("found", "найденные"), ("export", "скачать список"),
            ("delay", "пауза между проверками"), ("help", "помощь"),
        ]])
    except Exception as e:  # noqa: BLE001
        log.warning("set_my_commands: %s", e)
    try:
        signal.signal(signal.SIGTERM, shutdown)
    except (ValueError, AttributeError):
        pass
    resume_saved_jobs()
    log.info("Жду сообщений. Ctrl+C — выход.")
    try:
        bot.infinity_polling(skip_pending=True)
    except KeyboardInterrupt:
        shutdown()


if __name__ == "__main__":
    main()
