#!/usr/bin/env python3
"""
Telegram-бот: ищет СВОБОДНЫЕ редкие ники Roblox.
- Генерация ников через Google Gemini (официальный SDK), пачками до 1500
- Автоматический парсинг и проверка БЕСПЛАТНЫХ HTTP/SOCKS5 прокси (до 3000 за раз + авто-пополнение)
- Оценка ников (грейд S-D и редкость), команда /rate
- Работает на Render и в PyCharm

Установка: pip install pyTelegramBotAPI "requests[socks]" redis google-genai
Переменные окружения: TG_BOT_TOKEN, TG_CHAT_ID, AI_API_KEY, (PROXIES, REDIS_URL, PORT, CHECK_DELAY)
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
from concurrent.futures import ThreadPoolExecutor, as_completed
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import requests
from requests.adapters import HTTPAdapter
import telebot
from telebot import types

try:
    from google import genai
    from google.genai import types as gtypes

    AI_ENABLED = True
except ImportError:
    genai = None
    gtypes = None
    AI_ENABLED = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(message)s", datefmt="%H:%M:%S")
log = logging.getLogger("robloxbot")
for _noisy in ("httpx", "httpcore", "google_genai", "urllib3", "TeleBot"):
    logging.getLogger(_noisy).setLevel(logging.WARNING)

# ===== НАСТРОЙКИ =====
TOKEN = ""  # Токен от @BotFather (или переменная TG_BOT_TOKEN)
ADMIN_ID = 0  # Твой ID (или переменная TG_CHAT_ID)
# =====================

TOKEN = TOKEN or os.environ.get("TG_BOT_TOKEN", "")

AI_API_KEY = os.environ.get("AI_API_KEY", "")
ai_client = (genai.Client(api_key=AI_API_KEY, http_options=gtypes.HttpOptions(timeout=20000))
             if AI_API_KEY and AI_ENABLED else None)


def _parse_ids(*chunks):
    ids = set()
    for chunk in chunks:
        for part in re.split(r"[,\s;]+", str(chunk or "")):
            if part.lstrip("-").isdigit() and int(part) != 0:
                ids.add(int(part))
    return ids


ADMIN_IDS = _parse_ids(ADMIN_ID, os.environ.get("TG_CHAT_ID", ""))

DELAY = float(os.environ.get("CHECK_DELAY", "0.15"))
MIN_DELAY, MAX_DELAY = 0.02, 15.0
MAX_AUTO_DELAY = 5.0
MAX_ERRORS = 400
MAX_WORDS = 5000
MAX_QUICK = 25
MAX_THREADS = 12
PANEL_EVERY = 10
SAVE_EVERY = 30
AI_DEFAULT = 300
AI_MAX = 1500
AI_BATCH = 500
FOUND_FILE = "found.txt"
CHECKED_FILE = "checked.txt"
STATE_FILE = "state.json"
PROXY_FILE = "proxies.txt"
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

bot = telebot.TeleBot(TOKEN, threaded=True)
ApiError = getattr(getattr(telebot, "apihelper", None), "ApiTelegramException", Exception)

jobs = {}
jobs_lock = threading.Lock()
state_lock = threading.RLock()
file_lock = threading.Lock()
SHUTTING_DOWN = threading.Event()
_delay_lock = threading.Lock()
_scraping_proxies = threading.Event()
_last_auto_scrape = 0.0


# ============================ ХРАНИЛИЩЕ ============================

class Storage:
    def __init__(self):
        self.redis = None
        url = os.environ.get("REDIS_URL", "").strip()
        if url:
            try:
                import redis
                self.redis = redis.from_url(url, decode_responses=True, socket_timeout=10)
                self.redis.ping()
                log.info("Хранилище: Redis")
            except Exception as e:
                log.warning("Redis недоступен (%s) — использую файл %s", e, STATE_FILE)
                self.redis = None

    @property
    def durable(self):
        return self.redis is not None or not ON_RENDER

    def load(self):
        data = {}
        raw = None
        try:
            if self.redis is not None:
                raw = self.redis.get(REDIS_KEY)
            else:
                with open(STATE_FILE, encoding="utf-8") as f:
                    raw = f.read()
            data = json.loads(raw) if raw else {}
        except FileNotFoundError:
            pass
        except Exception as e:
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
        except Exception as e:
            log.warning("Не удалось сохранить состояние: %s", e)


storage = Storage()
state = storage.load()
state.setdefault("jobs", {})
state.setdefault("found", [])
state.setdefault("min_notify_score", 60)
state.setdefault("auto_proxy", True)
ai_last_queries = {}
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
        with _delay_lock:
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


# ============================ БЕСПЛАТНЫЕ ПРОКСИ И АВТО-ОБНОВЛЕНИЕ ============================

FREE_PROXY_SOURCES = [
    ("http", "https://api.proxyscrape.com/v2/?request=displayproxies&protocol=http&timeout=3000&country=all&ssl=all&anonymity=all"),
    ("socks5h", "https://api.proxyscrape.com/v2/?request=displayproxies&protocol=socks5&timeout=3000&country=all"),
    ("http", "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt"),
    ("socks5h", "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/socks5.txt"),
    ("http", "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt"),
    ("socks5h", "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/socks5.txt"),
    ("http", "https://raw.githubusercontent.com/hookzof/socks5_list/master/proxy.txt"),
]


def _test_single_proxy(proxy_url):
    """Проверяет, открывает ли прокси API Roblox быстро и без 429."""
    try:
        r = requests.get(
            URL,
            params={"Username": "roblox", "Birthday": BIRTHDAY, "Context": "Signup"},
            proxies={"http": proxy_url, "https": proxy_url},
            timeout=(2.0, 2.5),
            headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
        )
        if r.status_code == 200 and "code" in r.json():
            return proxy_url
    except Exception:
        pass
    return None


def scrape_and_check_free_proxies(max_test=3000, max_working=250):
    """Скачивает до 3000 публичных прокси и отбирает рабочие для Roblox."""
    candidates = []
    ip_port_re = re.compile(r"\b(?:\d{1,3}\.){3}\d{1,3}:\d{2,5}\b")

    for proto, src_url in FREE_PROXY_SOURCES:
        try:
            r = requests.get(src_url, timeout=8)
            if r.status_code == 200:
                found = ip_port_re.findall(r.text)
                candidates.extend(f"{proto}://{hp}" for hp in found)
        except Exception as e:
            log.warning("Ошибка загрузки прокси с %s: %s", src_url[:45], e)

    candidates = list(dict.fromkeys(candidates))
    random.shuffle(candidates)
    candidates = candidates[:max_test]

    working = []
    if not candidates:
        return 0, []

    with ThreadPoolExecutor(max_workers=60) as ex:
        futures = [ex.submit(_test_single_proxy, p) for p in candidates]
        for fut in as_completed(futures):
            if SHUTTING_DOWN.is_set():
                break
            res = fut.result()
            if res:
                working.append(res)
                if len(working) >= max_working:
                    for f in futures:
                        f.cancel()
                    break

    if working:
        existing = load_proxies()
        merged = list(dict.fromkeys(existing + working))
        with file_lock:
            try:
                with open(PROXY_FILE, "w", encoding="utf-8") as f:
                    f.write("\n".join(merged) + "\n")
            except OSError as e:
                log.warning("Не удалось сохранить %s: %s", PROXY_FILE, e)

    return len(candidates), working


def load_proxies():
    """Загружает HTTP/SOCKS5 прокси из переменной окружения PROXIES или файла proxies.txt."""
    raw_lines = []
    env_proxies = os.environ.get("PROXIES", "").strip()
    if env_proxies:
        raw_lines.extend(re.split(r"[\s,;]+", env_proxies))
    elif os.path.exists(PROXY_FILE):
        try:
            with open(PROXY_FILE, encoding="utf-8") as f:
                raw_lines.extend(line.strip() for line in f)
        except OSError as e:
            log.warning("Не удалось прочитать %s: %s", PROXY_FILE, e)

    cleaned = []
    for line in raw_lines:
        if not line or line.startswith("#"):
            continue
        if "://" not in line:
            line = "http://" + line
        cleaned.append(line)
    return list(dict.fromkeys(cleaned))


class SessionPool:
    def __init__(self, min_size=MAX_THREADS):
        self._lock = threading.Lock()
        self._sessions = []
        self._idx = 0
        self.proxy_count = 0
        self.reload(min_size)

    def _build_session(self, proxy_url=None):
        s = requests.Session()
        adapter = HTTPAdapter(pool_connections=10, pool_maxsize=20, max_retries=0)
        s.mount("https://", adapter)
        s.mount("http://", adapter)
        s.headers.update({
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Accept-Encoding": "gzip, deflate",
            "Connection": "keep-alive",
        })
        if proxy_url:
            s.proxies.update({"http": proxy_url, "https": proxy_url})
            s._proxy_url = proxy_url
        else:
            s._proxy_url = None
        return s

    def reload(self, min_size=MAX_THREADS):
        proxies = load_proxies()
        new_sessions = []
        if proxies:
            for p in proxies:
                new_sessions.append(self._build_session(p))
        else:
            for _ in range(min_size):
                new_sessions.append(self._build_session(None))

        with self._lock:
            for old_s in self._sessions:
                try:
                    old_s.close()
                except Exception:
                    pass
            self._sessions = new_sessions
            self._idx = 0
            self.proxy_count = len(proxies)

        if proxies:
            log.info("Загружено прокси: %d", len(proxies))
        else:
            log.info("Прокси не заданы — работаю напрямую с IP сервера")
        return len(proxies)

    def drop_bad(self, bad_session):
        """Удаляет умерший бесплатный прокси из пула на лету и обновляет файл."""
        bad_url = getattr(bad_session, "_proxy_url", None)
        if not bad_url:
            return
        with self._lock:
            if bad_session in self._sessions:
                self._sessions.remove(bad_session)
                try:
                    bad_session.close()
                except Exception:
                    pass
                alive_urls = [getattr(s, "_proxy_url", None) for s in self._sessions if getattr(s, "_proxy_url", None)]
                self.proxy_count = len(alive_urls)

                if not alive_urls:
                    self._sessions = [self._build_session(None) for _ in range(MAX_THREADS)]
                    self.proxy_count = 0

                with file_lock:
                    try:
                        with open(PROXY_FILE, "w", encoding="utf-8") as f:
                            f.write(("\n".join(alive_urls) + "\n") if alive_urls else "")
                    except OSError:
                        pass

    def get(self):
        with self._lock:
            s = self._sessions[self._idx % len(self._sessions)]
            self._idx += 1
            return s


session_pool = SessionPool(MAX_THREADS)


def run_free_proxy_task(chat_id=None, silent=False):
    """Запускает сбор до 3000 прокси в фоне (ручной или автоматический)."""
    global _last_auto_scrape
    if _scraping_proxies.is_set():
        if chat_id and not silent:
            say(chat_id, "⏳ Поиск бесплатных прокси уже запущен, подожди 20–30 сек...")
        return
    _scraping_proxies.set()
    _last_auto_scrape = time.time()

    if chat_id and not silent:
        say(chat_id, "🌐 Собираю до 3000 бесплатных HTTP/SOCKS5 прокси и проверяю их на доступ к Roblox (~30–45 сек)...")
    else:
        log.info("Авто-пополнение прокси: начинаю парсинг до 3000 узлов...")

    def worker():
        try:
            tested, working = scrape_and_check_free_proxies(max_test=3000, max_working=250)
            total_now = session_pool.reload(MAX_THREADS)
            if working:
                log.info("Авто-пополнение прокси: найдено %d рабочих (всего в пуле: %d)", len(working), total_now)
                if chat_id:
                    say(chat_id,
                        f"🌐 <b>Пул прокси обновлён!</b>\n"
                        f"Проверено: {tested} · Найдено живых: <b>+{len(working)}</b> (всего активных: <b>{total_now}</b>)",
                        silent=silent)
            else:
                log.warning("Авто-пополнение прокси: живых узлов не найдено из %d", tested)
                if chat_id and not silent:
                    say(chat_id,
                        f"⚠️ Из {tested} бесплатных прокси ни один не ответил быстро.\n"
                        f"Бот продолжает работать через текущий IP.")
        finally:
            _scraping_proxies.clear()

    threading.Thread(target=worker, daemon=True).start()


def maybe_auto_refill_proxies(chat_id):
    """Автоматически запускает поиск новых прокси, если в пуле осталось <= 2 живых."""
    if not state.get("auto_proxy", True):
        return
    if _scraping_proxies.is_set():
        return
    if session_pool.proxy_count > 2:
        return
    if time.time() - _last_auto_scrape < 90:
        return
    run_free_proxy_task(chat_id=chat_id, silent=True)


# ============================ НИКИ И АЛГОРИТМЫ ============================

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


def variant_names(word):
    LEET = {"a": "4", "e": "3", "i": "1", "o": "0", "s": "5", "t": "7", "b": "8", "g": "9", "l": "1"}
    PREFIXES = ["x", "xx", "xo", "mr", "its", "im", "the", "real", "pro", "my", "ur", "i"]
    SUFFIXES = ["x", "xx", "xd", "hd", "gg", "tv", "yt", "pro", "official", "rbx", "rblx",
                "zz", "007", "123", "_x", "_gg"]
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


def cvcv_names():
    """Все 4-буквенные комбинации CVCV и VCVC (согласная+гласная чередованием)."""
    cons = [c for c in LETTERS if c not in VOWELS]
    vows = list(VOWELS)
    out = []
    for c1, v1, c2, v2 in itertools.product(cons, vows, cons, vows):
        out.append(c1 + v1 + c2 + v2)
    for v1, c1, v2, c2 in itertools.product(vows, cons, vows, cons):
        out.append(v1 + c1 + v2 + c2)
    rng = random.Random(42)
    rng.shuffle(out)
    return [x for x in dict.fromkeys(out) if valid_format(x)]


def patterns_20l():
    """Генерирует идеальные математические паттерны длиной ровно 20 символов."""
    alphabet = LETTERS + DIGITS
    out = []

    for ch in alphabet:
        out.append(ch * 20)

    for a in alphabet:
        for b in alphabet:
            if a != b:
                out.append((a + b) * 10)

    for a in LETTERS:
        for b in LETTERS:
            if a != b:
                out.append((a * 2 + b * 2) * 5)

    for a in LETTERS:
        for b in LETTERS:
            if a != b:
                out.append(a * 10 + b * 10)

    for root in cvcv_names()[:150]:
        out.append(root * 5)

    roots5 = ["qwert", "asdfg", "zxcvb", "shado", "ghost", "night", "frost", "flame",
              "venom", "viper", "raven", "tiger", "chaos", "omega", "alpha", "titan", "nexus"]
    for root in roots5:
        out.append(root * 4)

    return [x for x in dict.fromkeys(out) if len(x) == 20 and valid_format(x)]


def make_names(spec):
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
    if kind == "cvcv":
        return iter(cvcv_names()[pos:])
    if kind == "p20":
        return iter(patterns_20l()[pos:])
    raise ValueError(f"Неизвестный тип задачи: {kind}")


# ============================ ОЦЕНКА НИКОВ ============================

OG_WORDS = {
    "fire", "ice", "dark", "light", "king", "queen", "wolf", "fox", "star", "moon", "sun", "storm",
    "night", "ghost", "angel", "devil", "dragon", "shadow", "blade", "ninja", "hero", "zero", "neo",
    "nova", "luna", "echo", "frost", "flame", "venom", "viper", "raven", "hawk", "tiger", "lion",
    "bear", "wild", "cool", "epic", "rich", "gold", "silver", "iron", "steel", "stone", "rock",
    "wind", "rain", "snow", "sky", "sea", "wave", "ash", "onyx", "ruby", "jade", "zen", "ace",
    "void", "abyss", "chaos", "omega", "alpha", "titan", "atlas", "zeus", "ares", "hades", "odin",
    "thor", "loki", "vale", "dawn", "dusk", "mist", "haze", "spark", "volt", "flux", "nexus", "apex",
    "max", "rex", "kai", "leo", "ivy", "eli", "ray", "sam", "alex", "jack", "john", "mike", "anna",
}


def _load_dict():
    dict_path = "words_en.txt"
    if not os.path.exists(dict_path):
        try:
            r = requests.get(
                "https://raw.githubusercontent.com/dwyl/english-words/master/words_alpha.txt",
                timeout=10
            )
            if r.status_code == 200:
                words = [w.strip().lower() for w in r.text.splitlines() if
                         3 <= len(w.strip()) <= 12 and w.strip().isalpha()]
                with open(dict_path, "w", encoding="utf-8") as f:
                    f.write("\n".join(words))
        except Exception as e:
            log.warning("Не удалось скачать словарь: %s", e)
            return set(OG_WORDS)

    try:
        with open(dict_path, encoding="utf-8") as f:
            return {line.strip().lower() for line in f if line.strip()} | OG_WORDS
    except Exception:
        return set(OG_WORDS)


ALL_WORDS = _load_dict()
VOWELS = "aeiouy"
LEN_POINTS = {3: 45, 4: 40, 5: 32, 6: 12, 7: 6, 8: 4, 9: 2}
CONFUSABLE = ("il", "li", "ll", "rn", "1l", "l1", "o0", "0o", "iii", "lll")


def _pronounceable(s):
    if len(s) < 2 or not any(c in VOWELS for c in s):
        return False
    cons = vow = 0
    for c in s:
        if c in VOWELS:
            vow += 1
            cons = 0
        else:
            cons += 1
            vow = 0
        if cons >= 3 or vow >= 3:
            return False
    return True


def _pattern_points(n):
    L = len(n)
    if L < 3:
        return 0, ""
    if len(set(n)) == 1:
        return 25, "повтор"
    diffs = {ord(n[i + 1]) - ord(n[i]) for i in range(L - 1)}
    if n.isalpha() and diffs in ({1}, {-1}):
        return 22, "алфавитный ряд"
    for row in KEY_ROWS:
        if n in row or n[::-1] in row:
            return 22, "ряд клавиатуры"
    if len(set(n)) == 2 and L >= 4 and all(n[i] == n[i % 2] for i in range(L)):
        return 20, "чередование"
    if n == n[::-1]:
        return 20, "палиндром"
    if L % 2 == 0 and n[:L // 2] == n[L // 2:]:
        return 16, "двойной повтор"
    return 0, ""


def rate_name(name):
    n = name.lower()
    L = len(n)
    core = re.sub(r"[0-9_]", "", n)

    length = LEN_POINTS.get(L, 0)

    if core in OG_WORDS:
        meaning = 40
    elif core in ALL_WORDS:
        meaning = 35
    elif _pronounceable(core):
        meaning = 8
    else:
        meaning = 0

    pattern, pattern_name = _pattern_points(n)

    if "_" in n:
        chars = 3
    elif any(c.isdigit() for c in n):
        digit_inside = bool(re.search(r"[a-z][0-9]+[a-z]", n))
        chars = 2 if digit_inside else 6
    else:
        chars = 15

    penalty = 0
    if any(p in n for p in CONFUSABLE):
        penalty += 5
    if re.search(r"(.)\1\1", n) and len(set(n)) > 1:
        penalty += 5

    if L == 20 and pattern >= 16:
        length = 45

    score = max(0, min(100, length + meaning + pattern + chars - penalty))

    if score >= 85:
        grade, rarity = "S", "💎 Очень редкий"
    elif score >= 70:
        grade, rarity = "A", "🔥 Редкий"
    elif score >= 55:
        grade, rarity = "B", "✨ Необычный"
    elif score >= 38:
        grade, rarity = "C", "🙂 Обычный"
    else:
        grade, rarity = "D", "🗑 Не редкий"

    return {"score": score, "grade": grade, "rarity": rarity, "pattern": pattern_name,
            "parts": (length, meaning, pattern, chars, 0, penalty)}


def rating_line(name):
    r = rate_name(name)
    return f"{r['rarity']} · {r['grade']} ({r['score']}/100)"


def rating_report(name):
    r = rate_name(name)
    ln, me, pa, ch, _, pen = r["parts"]
    pat = f" ({r['pattern']})" if r["pattern"] else ""
    return (f"<code>{html.escape(name)}</code> — {r['rarity']}\n"
            f"Оценка: <b>{r['grade']}</b> · {r['score']}/100\n"
            f"Длина {ln}/45 · Словарь {me}/40 · Паттерн {pa}/25{pat}\n"
            f"Символы {ch}/15 · Штраф −{pen}")


# ============================ ИИ ГЕНЕРАТОР (GOOGLE GENAI) ============================

PREFERRED_MODELS = ["gemini-3.1-flash-lite", "gemini-3.5-flash-lite", "gemini-3.5-flash"]
_models_cache = []
_bad_until = {}
_good_model = None


def pick_models():
    global _models_cache
    if not _models_cache:
        try:
            available = [m.name.replace("models/", "") for m in ai_client.models.list()]
        except Exception as e:
            log.warning("Не удалось получить список моделей: %s", e)
            available = []
        if available:
            chosen = [m for m in PREFERRED_MODELS if m in available]
            extra = [m for m in available
                     if m.startswith("gemini-") and "flash" in m
                     and not m.startswith("gemini-2")
                     and m not in chosen
                     and not any(x in m for x in ("image", "tts", "live", "audio", "embedding"))]
            _models_cache = chosen + extra[:3]
        else:
            return list(PREFERRED_MODELS)

    now = time.time()
    models = [m for m in _models_cache if _bad_until.get(m, 0) <= now]
    if _good_model in models:
        models.remove(_good_model)
        models.insert(0, _good_model)
    return models or list(_models_cache)


def _mark_bad(model_name, err):
    msg = str(err)
    if "404" in msg or "NOT_FOUND" in msg:
        _bad_until[model_name] = float("inf")
    elif any(x in msg for x in ("503", "UNAVAILABLE", "429", "RESOURCE_EXHAUSTED")):
        _bad_until[model_name] = time.time() + 120


def run_ai_search(chat_id, topic, count):
    ai_last_queries[chat_id] = (topic, count)
    say(chat_id, f"🧠 Gemini генерирует до {count} редких слов по теме: <b>{html.escape(topic)}</b>...")

    def process_ai():
        names, err = generate_ai_names(topic, count)
        if not names:
            say(chat_id, f"❌ Gemini не ответил.\n<code>{html.escape(err or '')}</code>")
            return
        say(chat_id, f"✅ ИИ подобрал {len(names)} слов. Запускаю проверку...")
        begin(chat_id,
              new_spec("words", f"ИИ (Gemini): {topic}", len(names), words=names, ai_topic=topic, ai_count=count))

    threading.Thread(target=process_ai, daemon=True).start()


def generate_ai_names(prompt_topic, count=AI_DEFAULT):
    global _good_model
    if not ai_client:
        return [], "AI_API_KEY не задан или не установлен google-genai"

    count = min(max(count, 1), AI_MAX)
    config = gtypes.GenerateContentConfig(max_output_tokens=8192, temperature=1.0)
    names, errors = [], []
    rounds = 0

    while len(names) < count and rounds < 8:
        rounds += 1
        want = min(AI_BATCH, count - len(names) + 40)
        avoid = ", ".join(names[-40:])
        avoid_rule = f"\n5. AVOID DUPLICATES: Do NOT include any of these: {avoid}" if avoid else ""
        prompt = (
            f"You are an expert lexicographer and rare username hunter.\n"
            f"Theme/concept: '{prompt_topic}'. Generate {want} real, rare English dictionary words related to this theme.\n\n"
            f"STRICT RULES:\n"
            f"1. REAL DICTIONARY WORDS ONLY: Output ONLY genuine, existing English words (nouns, adjectives, archaic, scientific, astronomical, chemical, botanical, or medical terms). DO NOT invent fake fantasy words.\n"
            f"2. SHORT LENGTH: Strictly 5 or 6 letters long (a few 4 or 7 letter rare terms are acceptable, but prioritize 5–6 letters).\n"
            f"3. CLEAN LETTERS ONLY: Only Latin letters (A-Z). No numbers, no underscores, no prefixes/suffixes.\n"
            f"4. OUTPUT FORMAT: Return ONLY raw lowercase words separated by spaces or newlines. No numbering, no bullets, no explanations.{avoid_rule}"
        )
        got = False
        for model_name in pick_models():
            try:
                resp = ai_client.models.generate_content(
                    model=model_name, contents=prompt, config=config)
                words = re.findall(r"[A-Za-z0-9_]{3,20}", resp.text or "")
                fresh = [w.lower() for w in words if valid_format(w.lower())]
                before = len(names)
                names = list(dict.fromkeys(names + fresh))
                if len(names) > before:
                    _good_model = model_name
                    got = True
                    break
                errors.append(f"{model_name}: пустой ответ")
            except Exception as e:
                _mark_bad(model_name, e)
                errors.append(f"{model_name}: {str(e)[:120]}")
                log.warning("Gemini %s: %s", model_name, str(e)[:150])
        if not got:
            break
        if len(names) < count:
            time.sleep(1)

    names = names[:count]
    if names:
        return names, None
    return [], "\n".join(errors[-3:])


# ============================ ФОРМАТИРОВАНИЕ И СТАТИСТИКА ============================

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


# ============================ ПРОВЕРКА ROBLOX API ============================

def check(session, name, stop, info=None):
    info = info if info is not None else {}
    has_proxies = session_pool.proxy_count > 0
    retries = 2 if has_proxies else 3
    backoff = 0.5

    for attempt in range(retries):
        if stop.is_set():
            return "stopped"
        try:
            r = session.get(
                URL,
                params={"Username": name, "Birthday": BIRTHDAY, "Context": "Signup"},
                timeout=(2.5, 3.5),
            )
        except requests.RequestException:
            info["last_http"] = "ошибка сети/прокси"
            if has_proxies:
                session_pool.drop_bad(session)
                session = session_pool.get()
                continue
            stop.wait(backoff)
            backoff = min(backoff * 2, 10)
            continue

        if r.status_code == 429:
            info["limited"] = info.get("limited", 0) + 1
            if has_proxies:
                session_pool.drop_bad(session)
                return "limited"
            try:
                wait = int(r.headers.get("Retry-After", backoff))
            except (TypeError, ValueError):
                wait = backoff
            stop.wait(min(max(wait, 0.5), 30))
            return "limited"

        if r.status_code != 200:
            if has_proxies:
                session_pool.drop_bad(session)
                if attempt + 1 < retries:
                    session = session_pool.get()
                    continue
            return "error"

        try:
            code = r.json().get("code")
        except ValueError:
            return "error"
        if code == 0:
            return "free"
        if code == 1:
            return "taken"
        return "blocked"
    return "error"


def tg(fn, *args, **kwargs):
    for _ in range(2):
        try:
            return fn(*args, **kwargs)
        except ApiError as e:
            if "message is not modified" in str(e):
                return None
            if getattr(e, "error_code", None) == 429:
                time.sleep(2)
                continue
            return None
        except Exception:
            return None
    return None


def say(chat_id, text, markup=None, silent=False):
    return tg(bot.send_message, chat_id, text, parse_mode="HTML",
              reply_markup=markup, disable_notification=silent)


def button(text, data=None, url=None):
    return types.InlineKeyboardButton(text=text, callback_data=data, url=url)


def main_menu():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("💎 Все CVCV (4 буквы)", "m:cvcv"), button("🔁 Паттерны 20L", "m:p20"))
    kb.row(button("🔍 Все 4 буквы", "m:all4"), button("🔍 Все 5 букв", "m:all5"))
    kb.row(button("✨ Красивые 4", "m:pr4"), button("📊 Статус", "m:status"))
    kb.row(button("⏹ Стоп", "stop"), button("▶️ Продолжить", "m:resume"))
    kb.row(button("📋 Найденные", "m:found"), button("📤 Экспорт", "m:export"), button("⚙️ Настройки", "m:set"))
    return kb


def settings_text():
    with _delay_lock:
        d = DELAY
    ms = state.get("min_notify_score", 60)
    grade_lbl = {0: "Все (D+)", 38: "Обычные (C+)", 55: "Необычные (B+)", 70: "Редкие (A+)", 85: "Только S"}.get(ms, f"от {ms}")
    px = session_pool.proxy_count
    px_text = f"<b>{px} живых</b>" if px else "0 (прямой IP)"
    auto_lbl = "ВКЛ ✅" if state.get("auto_proxy", True) else "ВЫКЛ ❌"
    return (f"⚙️ <b>Настройки бота</b>\n\n"
            f"⏱ Пауза: <b>{d:.2f} с</b> (потоков: {MAX_THREADS})\n"
            f"🌐 Прокси: {px_text} · Авто-сбор: <b>{auto_lbl}</b>\n"
            f"🔔 Уведомлять о никах: <b>{grade_lbl}</b> (≥ {ms} баллов)\n"
            f"<i>Ники ниже порога всё равно сохраняются в /found</i>")


def settings_markup():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("➖ 0.05 с", "dl:-"), button("➕ 0.05 с", "dl:+"), button("🤖 Авто-прокси", "px:auto"))
    kb.row(button("🆓 Найти прокси (3000)", "px:free"), button("🔄 Перечитать файл", "px:reload"))
    kb.row(
        button("Все (0)", "nt:0"),
        button("C+ (38)", "nt:38"),
        button("B+ (55)", "nt:55"),
        button("A+ (70)", "nt:70"),
    )
    return kb


def panel_markup():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("⏹ Стоп", "stop"), button("🔄 Обновить", "refresh"))
    return kb


def new_spec(kind, title, total, **extra):
    spec = {"kind": kind, "title": title, "total": total, "pos": 0, "running": True,
            "stats": {"checked": 0, "free": 0, "limited": 0}, "created": time.time()}
    spec.update(extra)
    return spec


def new_job(spec):
    return {"stop": threading.Event(), "spec": spec, "t0": time.time(), "pos0": spec["pos"],
            "current": "ультра-поиск...", "delay": DELAY, "errors": 0,
            "limited": 0, "panel": None, "thread": None}


class Panel:
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
        with _delay_lock:
            delay = DELAY
        rate = moved / elapsed if (elapsed > 10 and moved >= 5) else MAX_THREADS / (delay + 0.1)
        eta = (total - pos) / rate if rate > 0 else 0
        head = {None: "⏳", "done": "🏁", "stopped": "⏸", "blocked": "⚠️", "crashed": "💥"}[status]
        if _scraping_proxies.is_set():
            px_tag = f" · прокси: {session_pool.proxy_count} (ищу новые...)"
        elif session_pool.proxy_count:
            px_tag = f" · прокси: {session_pool.proxy_count}"
        else:
            px_tag = ""
        lines = [
            f"{head} <b>{html.escape(spec['title'])}</b>",
            f"{bar(frac)} {frac * 100:.1f}%  ({num(pos)} из {num(total)})",
            f"🟢 Свободных: <b>{st['free']}</b>    ·    проверено: {num(st['checked'])}",
        ]
        if status is None:
            lines.append(f"⚡ ~{rate * 60:.0f} ников/мин (потоков: {MAX_THREADS}{px_tag})")
            lines.append(f"🕒 Осталось: {fmt_duration(eta)}")
        if st["limited"]:
            lines.append(f"🚦 Лимитов (429): {st['limited']}")
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
    min_score = state.get("min_notify_score", 60)
    score = rate_name(name)["score"]
    if score < min_score:
        return
    kb = types.InlineKeyboardMarkup()
    kb.row(button("🔄 Проверить", f"re:{name}"), button("✏️ Занять", url=ACCOUNT_URL))
    say(chat_id, f"🟢 <b>Свободен ник:</b> <code>{name}</code>\n{rating_line(name)}", kb)


def run_job(chat_id, job):
    spec = job["spec"]
    stats = spec["stats"]
    is_file_or_custom = spec["kind"] in ("words", "variants", "pretty", "scan", "p20")
    panel = Panel(chat_id, job)
    job["panel"] = panel
    panel.send()
    persist(force=True)

    # Если при старте пул прокси пуст — запускаем авто-сбор в фоне
    maybe_auto_refill_proxies(chat_id)

    base = spec["pos"]
    name_iterator = make_names(spec)
    retry_queue = []
    outcome = "done"

    def worker_check(args):
        idx, name = args
        if job["stop"].is_set():
            return idx, name, "stopped"
        session = session_pool.get()
        name = name.strip().lower()

        if not valid_format(name):
            return idx, name, "invalid"

        if not is_file_or_custom and name in checked:
            return idx, name, "skipped"

        job["current"] = name
        status = check(session, name, job["stop"], job)
        return idx, name, status

    try:
        chunk_size = MAX_THREADS * 6
        with ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
            while not job["stop"].is_set():
                # Автоматически пополняем прокси, когда живых остаётся <= 2
                maybe_auto_refill_proxies(chat_id)

                batch = []
                while retry_queue and len(batch) < chunk_size:
                    batch.append(retry_queue.pop(0))

                while len(batch) < chunk_size:
                    try:
                        name = next(name_iterator)
                        batch.append((base, name))
                        base += 1
                    except StopIteration:
                        break
                if not batch:
                    break

                futures = [executor.submit(worker_check, item) for item in batch]
                for future in as_completed(futures):
                    if job["stop"].is_set():
                        outcome = "stopped"
                        break
                    try:
                        idx, name, status = future.result()
                        if idx >= spec["pos"]:
                            spec["pos"] = idx + 1

                        if status == "stopped":
                            outcome = "stopped"
                            break
                        if status == "error":
                            job["errors"] += 1
                            if session_pool.proxy_count == 0:
                                job["delay"] = min(job["delay"] * 1.5 + 0.3, MAX_AUTO_DELAY)
                                job["stop"].wait(1.0)
                            else:
                                retry_queue.append((idx, name))
                            if job["errors"] >= MAX_ERRORS:
                                outcome = "blocked"
                                break
                            continue
                        if status == "limited":
                            stats["limited"] += 1
                            retry_queue.append((idx, name))
                            if session_pool.proxy_count == 0:
                                job["delay"] = min(job["delay"] * 1.2 + 0.1, MAX_AUTO_DELAY)
                            continue

                        job["errors"] = 0
                        if status in ("free", "taken", "blocked", "skipped", "invalid"):
                            if status not in ("skipped", "invalid"):
                                stats["checked"] += 1
                            if not is_file_or_custom and status not in ("skipped", "invalid"):
                                checked.add(name)
                                append_line(CHECKED_FILE, name)
                            if status == "free":
                                stats["free"] += 1
                                register_found(name)
                                announce(chat_id, name)

                        with _delay_lock:
                            current_delay = DELAY
                        job["delay"] = max(current_delay, job["delay"] * 0.98)

                    except Exception:
                        pass

                panel.update()
                persist()
                if job["delay"] > 0:
                    job["stop"].wait(job["delay"])

                if outcome != "done":
                    break

    except Exception:
        outcome = "crashed"
    finally:
        with jobs_lock:
            jobs.pop(chat_id, None)
        if SHUTTING_DOWN.is_set():
            spec["running"] = True
            persist(force=True)
        else:
            _finish_job(chat_id, job, outcome)


def _finish_job(chat_id, job, outcome):
    spec, stats = job["spec"], job["spec"]["stats"]
    if outcome == "done":
        with state_lock:
            state["jobs"].pop(str(chat_id), None)
    else:
        spec["running"] = False
    persist(force=True)
    job["panel"].update(force=True, status=outcome)
    tail = f"Проверено: {num(stats['checked'])}, свободных: {stats['free']}."
    markup = None

    if outcome == "done":
        text = f"🏁 Готово: {html.escape(spec['title'])}. {tail}\n/found"
        if "ai_topic" in spec:
            ai_last_queries[chat_id] = (spec["ai_topic"], spec.get("ai_count", AI_DEFAULT))
            markup = types.InlineKeyboardMarkup()
            markup.row(button("🔁 Следующая пачка ИИ", "ai_next"))
    elif outcome == "stopped":
        text = f"⏹ Остановлено на позиции {num(spec['pos'])}. {tail}\nПродолжить: /resume"
    else:
        text = f"⚠️ Превышен лимит ошибок. Пауза. {tail}\n/resume"
    say(chat_id, text, markup=markup)


def begin(chat_id, spec):
    with jobs_lock:
        busy = chat_id in jobs
        if not busy:
            job = new_job(spec)
            jobs[chat_id] = job
    if busy:
        say(chat_id, "Уже идет проверка. Смотри /status или останови /stop")
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
        "pretty", f"Красивые {n}-буквенные", len(names), length=n))


def resume_job(chat_id):
    spec = state["jobs"].get(str(chat_id))
    if chat_id in jobs:
        say(chat_id, "Проверка уже идет: /status")
    elif not spec:
        say(chat_id, "Нет приостановленных задач.")
    else:
        say(chat_id, f"▶️ Продолжаю: <b>{html.escape(spec['title'])}</b> с позиции {num(spec['pos'])}")
        begin(chat_id, spec)


def resume_saved_jobs():
    for cid, spec in list(state["jobs"].items()):
        if spec.get("running") and int(cid) not in jobs:
            begin(int(cid), spec)


def send_status(chat_id):
    job = jobs.get(chat_id)
    spec = state["jobs"].get(str(chat_id))
    if job:
        say(chat_id, job["panel"].text() + f"\nПроверяется: <code>{job['current']}</code>")
    elif spec:
        say(chat_id,
            f"⏸ На паузе: <b>{html.escape(spec['title'])}</b>\nПозиция: {num(spec['pos'])}\nПродолжить: /resume")
    else:
        say(chat_id, "Ничего не запущено. Открой /menu")


def stop_job(chat_id):
    job = jobs.get(chat_id)
    if not job:
        return False
    job["stop"].set()
    return True


def allowed(chat_id):
    return bool(ADMIN_IDS) and chat_id in ADMIN_IDS


def guard(m):
    if allowed(m.chat.id):
        return True
    if not ADMIN_IDS:
        tg(bot.reply_to, m, f"🔧 Твой chat id: <code>{m.chat.id}</code>. Впиши его в ADMIN_ID.", parse_mode="HTML")
    else:
        tg(bot.reply_to, m, f"⛔ Доступ закрыт. ID: <code>{m.chat.id}</code>", parse_mode="HTML")
    return False


HELP = (
    "<b>Бот для поиска редких ников в Roblox</b>\n\n"
    "/menu — главное меню\n"
    "/freeproxy — спарсить и проверить до 3000 бесплатных прокси\n"
    "/reload — перечитать proxies.txt\n"
    f"<code>/ai [число] [тема]</code> — подобрать редкие словарные слова через Gemini и проверить "
    f"(по умолчанию {AI_DEFAULT}, максимум {AI_MAX}). Пример: <code>/ai 500 astronomy</code>\n"
    "<code>/rate ник</code> — оценить реальную редкость ника\n"
    "<code>/name ник</code> — быстрая проверка ников\n"
    "/all4 /all5 — поиск по всем комбинациям\n"
    "/pretty 4 — красивый перебор\n"
    "<code>/variants слово</code> — варианты слова\n"
    "<code>/scan шаблон [кол-во]</code> — поиск по шаблону (? буква, # цифра)\n"
    "/status /stop /resume — управление задачами\n"
    "/found — список найденных, /export — файл\n"
    "/delay /notify — настройки скорости и уведомлений"
)


@bot.message_handler(commands=["id"])
def cmd_id(m):
    tg(bot.reply_to, m, f"Твой chat id: <code>{m.chat.id}</code>", parse_mode="HTML")


@bot.message_handler(commands=["start", "menu"])
def cmd_start(m):
    if guard(m):
        say(m.chat.id, "🤖 <b>Выбери режим поиска:</b>", main_menu())


@bot.message_handler(commands=["help"])
def cmd_help(m):
    if guard(m):
        say(m.chat.id, HELP)


@bot.message_handler(commands=["freeproxy"])
def cmd_freeproxy(m):
    if guard(m):
        run_free_proxy_task(m.chat.id, silent=False)


@bot.message_handler(commands=["reload"])
def cmd_reload(m):
    if not guard(m):
        return
    cnt = session_pool.reload(MAX_THREADS)
    say(m.chat.id, f"🌐 Пул обновлён. Загружено прокси: <b>{cnt}</b>")


@bot.message_handler(commands=["ai"])
def cmd_ai(m):
    if not guard(m):
        return
    if not ai_client:
        say(m.chat.id, "❌ ИИ не настроен! Проверь переменную <code>AI_API_KEY</code>.")
        return

    parts = m.text.split(maxsplit=1)
    rest = parts[1].strip() if len(parts) > 1 else ""
    count = AI_DEFAULT
    first, _, tail = rest.partition(" ")
    if first.isdigit():
        count = min(max(int(first), 10), AI_MAX)
        rest = tail.strip()
    topic = rest or "rare scientific and astronomical terms"
    run_ai_search(m.chat.id, topic, count)


@bot.message_handler(commands=["rate"])
def cmd_rate(m):
    if not guard(m):
        return
    names = [x.lower() for x in re.split(r"[\s,;]+", m.text)[1:] if valid_format(x.lower())]
    if not names:
        say(m.chat.id, "Использование: <code>/rate ник1 ник2</code>")
        return
    say(m.chat.id, "\n\n".join(rating_report(x) for x in names[:15]))


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
    if 3 <= n <= 6:
        start_pretty(m.chat.id, n)


@bot.message_handler(commands=["variants"])
def cmd_variants(m):
    if not guard(m):
        return
    parts = m.text.split()
    if len(parts) >= 2:
        word = parts[1].lower()
        names = variant_names(word)
        begin(m.chat.id, new_spec("variants", f"Варианты «{word}»", len(names), word=word))


@bot.message_handler(commands=["scan"])
def cmd_scan(m):
    if not guard(m):
        return
    args = m.text.split()[1:]
    if args:
        pattern = args[0].lower()
        n = int(args[1]) if len(args) > 1 and args[1].isdigit() else 0
        full = math.prod(len(o) for o in pattern_options(pattern))
        begin(m.chat.id,
              new_spec("scan", f"Шаблон {pattern}", n or full, pattern=pattern, n=n, seed=random.randrange(2 ** 31)))


@bot.message_handler(content_types=["document"])
def on_document(m):
    if not guard(m):
        return
    doc = m.document
    if (doc.file_name or "").lower().endswith(".txt"):
        data = tg(lambda: bot.download_file(bot.get_file(doc.file_id).file_path))
        if data:
            names = list(
                dict.fromkeys(x.strip().lower() for x in data.decode("utf-8", "ignore").splitlines() if x.strip()))[
                :MAX_WORDS]
            if names:
                begin(m.chat.id, new_spec("words", f"Файл {doc.file_name}", len(names), words=names))


def quick_check(chat_id, names):
    never = threading.Event()
    lines = []
    for name in names[:MAX_QUICK]:
        if not valid_format(name):
            lines.append(f"⚪ <code>{html.escape(name)}</code> — неверный формат")
            continue
        session = session_pool.get()
        st = check(session, name, never)
        label = {
            "free": f"🟢 <code>{name}</code> — свободен · {rating_line(name)}",
            "taken": f"🔴 <code>{name}</code> — занят",
            "blocked": f"⛔ <code>{name}</code> — запрещен",
        }.get(st, f"⚠️ <code>{name}</code> — ошибка")
        lines.append(label)
        time.sleep(0.05)
    say(chat_id, "\n".join(lines))


def start_quick(chat_id, names):
    names = list(dict.fromkeys(n.lower() for n in names if n))
    if names:
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
    if guard(m):
        stop_job(m.chat.id)
        tg(bot.reply_to, m, "Останавливаю...")


@bot.message_handler(commands=["resume"])
def cmd_resume(m):
    if guard(m):
        resume_job(m.chat.id)


def found_text():
    with state_lock:
        names = list(state["found"])
    if not names:
        return "Пока ничего не найдено"
    rated = sorted(names, key=lambda x: rate_name(x)["score"], reverse=True)[:50]
    lines = [f"<code>{x}</code> — {rating_line(x)}" for x in rated]
    return f"Найдено свободных: {len(names)} (топ по оценке):\n" + "\n".join(lines)


@bot.message_handler(commands=["found"])
def cmd_found(m):
    if guard(m):
        say(m.chat.id, found_text())


def send_export(chat_id):
    with state_lock:
        names = list(state["found"])
    if names:
        bio = io.BytesIO("\n".join(names).encode("utf-8"))
        bio.name = "found.txt"
        tg(bot.send_document, chat_id, bio)


@bot.message_handler(commands=["export"])
def cmd_export(m):
    if guard(m):
        send_export(m.chat.id)


def set_delay(value):
    global DELAY
    with _delay_lock:
        DELAY = round(min(max(value, MIN_DELAY), MAX_DELAY), 2)
    persist(force=True)
    return DELAY


@bot.message_handler(commands=["delay"])
def cmd_delay(m):
    if not guard(m):
        return
    parts = m.text.split()
    if len(parts) >= 2:
        try:
            set_delay(float(parts[1].replace(",", ".")))
        except ValueError:
            pass
    say(m.chat.id, settings_text(), settings_markup())


@bot.message_handler(func=lambda m: m.content_type == "text" and not (m.text or "").startswith("/"))
def on_text(m):
    if guard(m):
        tokens = [t for t in re.split(r"[\s,;]+", m.text.strip()) if t]
        if tokens and all(re.fullmatch(r"[A-Za-z0-9_]+", t) for t in tokens):
            start_quick(m.chat.id, tokens)
        else:
            say(m.chat.id, "Используй /menu или напиши ник")


@bot.message_handler(commands=["notify"])
def cmd_notify(m):
    if not guard(m):
        return
    parts = m.text.split()
    if len(parts) >= 2 and parts[1].isdigit():
        val = min(max(int(parts[1]), 0), 100)
        with state_lock:
            state["min_notify_score"] = val
        persist(force=True)
    say(m.chat.id, settings_text(), settings_markup())


@bot.callback_query_handler(func=lambda c: True)
def on_callback(c):
    chat_id = c.message.chat.id
    if not allowed(chat_id):
        tg(bot.answer_callback_query, c.id, "Нет доступа")
        return
    data = c.data or ""
    if data == "stop":
        stop_job(chat_id)
        tg(bot.answer_callback_query, c.id, "Останавливаю...")
    elif data == "refresh":
        job = jobs.get(chat_id)
        if job and job["panel"]:
            job["panel"].update(force=True)
            tg(bot.answer_callback_query, c.id, "Обновлено")
    elif data.startswith("re:"):
        tg(bot.answer_callback_query, c.id, "Проверяю...")
        start_quick(chat_id, [data[3:]])
    elif data in ("dl:+", "dl:-"):
        set_delay(DELAY + (0.05 if data == "dl:+" else -0.05))
        tg(bot.answer_callback_query, c.id, f"Пауза {DELAY:.2f}с")
        tg(bot.edit_message_text, settings_text(), chat_id=chat_id, message_id=c.message.message_id,
           parse_mode="HTML", reply_markup=settings_markup())
    elif data == "px:auto":
        with state_lock:
            state["auto_proxy"] = not state.get("auto_proxy", True)
        persist(force=True)
        tg(bot.answer_callback_query, c.id, "Авто-прокси переключено")
        tg(bot.edit_message_text, settings_text(), chat_id=chat_id, message_id=c.message.message_id,
           parse_mode="HTML", reply_markup=settings_markup())
    elif data == "px:free":
        tg(bot.answer_callback_query, c.id, "Запускаю сбор 3000 прокси...")
        run_free_proxy_task(chat_id, silent=False)
    elif data == "px:reload":
        cnt = session_pool.reload(MAX_THREADS)
        tg(bot.answer_callback_query, c.id, f"Прокси: {cnt}")
        tg(bot.edit_message_text, settings_text(), chat_id=chat_id, message_id=c.message.message_id,
           parse_mode="HTML", reply_markup=settings_markup())
    elif data.startswith("nt:"):
        val = int(data[3:])
        with state_lock:
            state["min_notify_score"] = val
        persist(force=True)
        tg(bot.answer_callback_query, c.id, f"Порог: ≥ {val}")
        tg(bot.edit_message_text, settings_text(), chat_id=chat_id, message_id=c.message.message_id,
           parse_mode="HTML", reply_markup=settings_markup())
    elif data == "ai_next":
        last = ai_last_queries.get(chat_id)
        if not last:
            tg(bot.answer_callback_query, c.id, "Тема не найдена, запусти /ai заново")
            return
        tg(bot.answer_callback_query, c.id, "Запускаю новую пачку...")
        run_ai_search(chat_id, last[0], last[1])
    elif data.startswith("m:"):
        tg(bot.answer_callback_query, c.id)
        action = data[2:]
        if action in ("all4", "all5"):
            start_all(chat_id, int(action[-1]))
        elif action in ("pr4", "pr5"):
            start_pretty(chat_id, int(action[-1]))
        elif action == "cvcv":
            names = cvcv_names()
            begin(chat_id, new_spec("cvcv", "Все 4 буквы CVCV/VCVC", len(names)))
        elif action == "p20":
            names = patterns_20l()
            begin(chat_id, new_spec("p20", "Паттерны 20 символов (20L)", len(names)))
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


class PingHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        self.send_response(200)
        self.end_headers()
        self.wfile.write(b"ok")

    def do_HEAD(self):
        self.send_response(200)
        self.end_headers()

    def log_message(self, *args):
        pass


def start_ping_server():
    port = os.environ.get("PORT")
    if port:
        server = ThreadingHTTPServer(("0.0.0.0", int(port)), PingHandler)
        threading.Thread(target=server.serve_forever, daemon=True).start()


def shutdown(signum=None, frame=None):
    if SHUTTING_DOWN.is_set():
        return
    SHUTTING_DOWN.set()
    for job in list(jobs.values()):
        job["stop"].set()
    persist(force=True)
    time.sleep(1)
    os._exit(0)


def main():
    start_ping_server()
    try:
        bot.delete_webhook(drop_pending_updates=True)
        time.sleep(1)
        me = bot.get_me()
    except Exception as e:
        raise SystemExit(f"Ошибка Telegram: {e}")

    log.info("Бот запущен: @%s", me.username)
    signal.signal(signal.SIGTERM, shutdown)
    signal.signal(signal.SIGINT, shutdown)
    resume_saved_jobs()

    try:
        bot.infinity_polling(skip_pending=True, interval=0.5, timeout=20)
    except KeyboardInterrupt:
        shutdown()


if __name__ == "__main__":
    main()
