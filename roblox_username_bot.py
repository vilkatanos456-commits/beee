#!/usr/bin/env python3
"""
Telegram-бот: ищет СВОБОДНЫЕ редкие ники Roblox.
- Генерация ников через Google Gemini (официальный SDK), пачками до 1500
- Оценка ников (грейд S-D и редкость), команда /rate
- Работает на Render и в PyCharm

Установка: pip install pyTelegramBotAPI requests redis google-genai
Переменные окружения: TG_BOT_TOKEN, TG_CHAT_ID, AI_API_KEY, (REDIS_URL, PORT, CHECK_DELAY)
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

DELAY = float(os.environ.get("CHECK_DELAY", "0.5"))
MIN_DELAY, MAX_DELAY = 0.05, 15.0
MAX_AUTO_DELAY = 5.0
MAX_ERRORS = 150
MAX_FULL = 20000
MAX_WORDS = 5000
MAX_QUICK = 25
MAX_THREADS = 4
PANEL_EVERY = 10
SAVE_EVERY = 30
AI_DEFAULT = 300
AI_MAX = 1500
AI_BATCH = 500
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

bot = telebot.TeleBot(TOKEN, threaded=True)
ApiError = getattr(getattr(telebot, "apihelper", None), "ApiTelegramException", Exception)

jobs = {}
jobs_lock = threading.Lock()
state_lock = threading.RLock()
file_lock = threading.Lock()
SHUTTING_DOWN = threading.Event()
_delay_lock = threading.Lock()


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
ai_last_queries = {}  # chat_id -> (topic, count)
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
    raise ValueError(f"Неизвестный тип задачи: {kind}")


def cvcv_names():
    """Все 4-буквенные комбинации CVCV и VCVC (согласная+гласная чередованием)."""
    cons = [c for c in LETTERS if c not in VOWELS]
    vows = list(VOWELS)
    out = []
    # CVCV (например, kuro, vexa)
    for c1, v1, c2, v2 in itertools.product(cons, vows, cons, vows):
        out.append(c1 + v1 + c2 + v2)
    # VCVC (например, alex, orin)
    for v1, c1, v2, c2 in itertools.product(vows, cons, vows, cons):
        out.append(v1 + c1 + v2 + c2)
    rng = random.Random(42)
    rng.shuffle(out)
    return [x for x in dict.fromkeys(out) if valid_format(x)]


# ============================ ОЦЕНКА НИКОВ ============================

# Базовый топ популярных OG-слов (максимальный бонус)
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
    """Загружает расширенный словарь английских слов (если есть файл words.txt или скачивает 1 раз)."""
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
LEN_POINTS = {3: 30, 4: 26, 5: 22, 6: 17, 7: 11, 8: 9, 9: 7}
CONFUSABLE = ("il", "li", "ll", "rn", "1l", "l1", "o0", "0o", "iii", "lll")

# Красивые фэнтези/латинские сочетания и редкие согласные
AESTHETIC_DIGRAPHS = ("ae", "yl", "th", "ix", "ex", "ox", "ax", "yn", "ys", "yr", "eo", "ia", "va", "zy", "vy")
RARE_LETTERS = set("vxzqky")


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


def _is_cvcvc(s):
    """Проверяет идеальное чередование согласная-гласная (типа K-a-v-o-n)."""
    if len(s) not in (4, 5, 6) or not s.isalpha():
        return False
    pattern = ["V" if c in VOWELS else "C" for c in s]
    return all(pattern[i] != pattern[i + 1] for i in range(len(pattern) - 1))


def _pattern_points(n):
    L = len(n)
    if L < 3:
        return 0, ""
    if len(set(n)) == 1:
        return 22, "повтор"
    diffs = {ord(n[i + 1]) - ord(n[i]) for i in range(L - 1)}
    if n.isalpha() and diffs in ({1}, {-1}):
        return 20, "алфавитный ряд"
    for row in KEY_ROWS:
        if n in row or n[::-1] in row:
            return 20, "ряд клавиатуры"
    if len(set(n)) == 2 and L >= 4 and all(n[i] == n[i % 2] for i in range(L)):
        return 18, "чередование"
    if n == n[::-1]:
        return 18, "палиндром"
    if L % 2 == 0 and n[:L // 2] == n[L // 2:]:
        return 15, "двойной повтор"
    if _is_cvcvc(n):
        return 10, "CVCVC-ритм"
    return 0, ""


def rate_name(name):
    """Возвращает dict: score, grade, rarity, pattern, parts."""
    n = name.lower()
    L = len(n)
    core = re.sub(r"[0-9_]", "", n)

    length = LEN_POINTS.get(L, 4)

    # 1. Смысл / словарность
    if core in OG_WORDS:
        meaning = 30
    elif core in ALL_WORDS:
        meaning = 24  # Настоящее редкое слово (как caelostat)
    elif _pronounceable(core):
        meaning = 14
    else:
        meaning = 4

    # 2. Паттерны и ритм
    pattern, pattern_name = _pattern_points(n)

    # 3. Чистота символов
    if "_" in n:
        chars = 4
    elif any(c.isdigit() for c in n):
        digit_inside = bool(re.search(r"[a-z][0-9]+[a-z]", n))
        chars = 2 if digit_inside else 7
    else:
        chars = 15

    # 4. Звучание и эстетика (бонус за редкие буквы и фэнтези-сочетания)
    sound = 0
    if _pronounceable(core):
        sound += 10 if L <= 7 else 6
        digraph_hits = sum(1 for d in AESTHETIC_DIGRAPHS if d in core)
        rare_hits = sum(1 for c in set(core) if c in RARE_LETTERS)
        sound += min(7, digraph_hits * 3 + rare_hits * 2)
    else:
        sound = 2

    # 5. Штрафы
    penalty = 0
    if any(p in n for p in CONFUSABLE):
        penalty += 5
    if re.search(r"(.)\1\1", n) and len(set(n)) > 1:
        penalty += 4
    if L >= 9 and meaning < 24:
        penalty += 4

    score = max(0, min(100, length + meaning + pattern + chars + sound - penalty))

    if score >= 88:
        grade, rarity = "S", "💎 Очень редкий"
    elif score >= 72:
        grade, rarity = "A", "🔥 Редкий"
    elif score >= 58:
        grade, rarity = "B", "✨ Необычный"
    elif score >= 40:
        grade, rarity = "C", "🙂 Обычный"
    else:
        grade, rarity = "D", "🗑 Не редкий"

    return {"score": score, "grade": grade, "rarity": rarity, "pattern": pattern_name,
            "parts": (length, meaning, pattern, chars, sound, penalty)}


def rating_line(name):
    r = rate_name(name)
    return f"{r['rarity']} · {r['grade']} ({r['score']}/100)"


def rating_report(name):
    r = rate_name(name)
    ln, me, pa, ch, so, pen = r["parts"]
    pat = f" ({r['pattern']})" if r["pattern"] else ""
    return (f"<code>{html.escape(name)}</code> — {r['rarity']}\n"
            f"Оценка: <b>{r['grade']}</b> · {r['score']}/100\n"
            f"Длина {ln}/30 · Смысл {me}/30 · Паттерн {pa}/22{pat}\n"
            f"Символы {ch}/15 · Звучание {so}/17 · Штраф −{pen}")

# ============================ ИИ ГЕНЕРАТОР (GOOGLE GENAI) ============================

PREFERRED_MODELS = ["gemini-3.1-flash-lite", "gemini-3.5-flash-lite", "gemini-3.5-flash"]
_models_cache = []
_bad_until = {}  # модель -> время, до которого её пропускаем
_good_model = None  # последняя модель, которая ответила


def pick_models():
    """Модели, доступные ключу. Рабочая идёт первой, мёртвые и перегруженные пропускаются."""
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
        _bad_until[model_name] = float("inf")  # модель не существует для ключа
    elif any(x in msg for x in ("503", "UNAVAILABLE", "429", "RESOURCE_EXHAUSTED")):
        _bad_until[model_name] = time.time() + 120  # перегружена, пропускаем 2 минуты


def run_ai_search(chat_id, topic, count):
    ai_last_queries[chat_id] = (topic, count)
    say(chat_id, f"🧠 Gemini генерирует до {count} ников по теме: <b>{html.escape(topic)}</b>...")

    def process_ai():
        names, err = generate_ai_names(topic, count)
        if not names:
            say(chat_id, f"❌ Gemini не ответил.\n<code>{html.escape(err or '')}</code>")
            return
        say(chat_id, f"✅ ИИ сгенерировал {len(names)} ников. Запускаю проверку...")
        begin(chat_id,
              new_spec("words", f"ИИ (Gemini): {topic}", len(names), words=names, ai_topic=topic, ai_count=count))

    threading.Thread(target=process_ai, daemon=True).start()


def generate_ai_names(prompt_topic, count=AI_DEFAULT):
    """Возвращает (names, error_text). Генерирует пачками, убирает дубли."""
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
        prompt = (
            f"You are a master gaming username designer.\n"
            f"Take the theme: '{prompt_topic}' and transform it into {count} rare, clean usernames.\n\n"
            f"STRICT RULES FOR GENERATION:\n"
            f"1. THEMATIC VARIATIONS: Derive unique roots, Latin/Greek stems, and stylistic variations from the concept '{prompt_topic}'.\n"
            f"2. TARGET LENGTHS: Strictly output names from 4 to 10 letters long (balanced mix of 4, 5, 6, 7, 8, 9, and 10 letters).\n"
            f"3. CLEAN ONLY: Only Latin letters (A-Z). ABSOLUTELY NO numbers, NO underscores, NO trash like 'xX', 'pro', 'yt', '123'.\n"
            f"4. PHONETICS: Must sound premium and pronounceable (e.g., theme 'shadow' -> 'gloom', 'umbra', 'nyxian', 'gloomix', 'shadowed').\n"
            f"5. OUTPUT FORMAT: Return ONLY raw usernames separated by spaces or newlines. No numbers, no markdown, no bullets."
        )
        got = False
        for model_name in pick_models():
            try:
                resp = ai_client.models.generate_content(
                    model=model_name, contents=prompt, config=config)
                words = re.findall(r"[A-Za-z0-9_]{3,15}", resp.text or "")
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
    backoff = 1
    for _ in range(3):
        if stop.is_set():
            return "stopped"
        try:
            r = session.get(
                URL,
                params={"Username": name, "Birthday": BIRTHDAY, "Context": "Signup"},
                timeout=5,
            )
        except requests.RequestException:
            info["last_http"] = "нет связи"
            stop.wait(backoff)
            backoff = min(backoff * 2, 10)
            continue

        if r.status_code == 429:
            info["limited"] = info.get("limited", 0) + 1
            try:
                wait = int(r.headers.get("Retry-After", backoff))
            except (TypeError, ValueError):
                wait = backoff
            stop.wait(min(max(wait, 0.5), 30))
            return "limited"

        if r.status_code != 200:
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


class SessionPool:
    def __init__(self, size):
        self._sessions = [requests.Session() for _ in range(size)]
        for s in self._sessions:
            s.headers.update({
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
                "Accept-Encoding": "gzip, deflate",
            })
        self._lock = threading.Lock()
        self._idx = 0

    def get(self):
        with self._lock:
            s = self._sessions[self._idx % len(self._sessions)]
            self._idx += 1
            return s


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
    kb.row(button("💎 Все CVCV (4 буквы)", "m:cvcv"), button("🔍 Все 4 буквы", "m:all4"))
    kb.row(button("🔍 Все 5 букв", "m:all5"), button("✨ Красивые 4", "m:pr4"))
    kb.row(button("📊 Статус", "m:status"), button("⏹ Стоп", "stop"), button("▶️ Продолжить", "m:resume"))
    kb.row(button("📋 Найденные", "m:found"), button("📤 Экспорт", "m:export"), button("⚙️ Настройки", "m:set"))
    return kb


def settings_text():
    with _delay_lock:
        d = DELAY
    ms = state.get("min_notify_score", 60)
    grade_lbl = {0: "Все (D+)", 40: "Обычные (C+)", 60: "Необычные (B+)", 75: "Редкие (A+)", 90: "Только S"}.get(ms,
                                                                                                                 f"от {ms}")
    return (f"⚙️ <b>Настройки бота</b>\n\n"
            f"⏱ Пауза: <b>{d:.2f} с</b> (потоков: {MAX_THREADS})\n"
            f"🔔 Уведомлять о никах: <b>{grade_lbl}</b> (≥ {ms} баллов)\n"
            f"<i>Ники ниже порога всё равно сохраняются в /found</i>")


def settings_markup():
    kb = types.InlineKeyboardMarkup()
    kb.row(button("➖ 0.1 с", "dl:-"), button("➕ 0.1 с", "dl:+"))
    kb.row(
        button("Все (0)", "nt:0"),
        button("C+ (40)", "nt:40"),
        button("B+ (60)", "nt:60"),
        button("A+ (75)", "nt:75"),
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
        lines = [
            f"{head} <b>{html.escape(spec['title'])}</b>",
            f"{bar(frac)} {frac * 100:.1f}%  ({num(pos)} из {num(total)})",
            f"🟢 Свободных: <b>{st['free']}</b>    ·    проверено: {num(st['checked'])}",
        ]
        if status is None:
            lines.append(f"⚡ ~{rate * 60:.0f} ников/мин (потоков: {MAX_THREADS})")
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
    is_file_or_custom = spec["kind"] in ("words", "variants", "pretty", "scan")
    panel = Panel(chat_id, job)
    job["panel"] = panel
    panel.send()
    persist(force=True)

    base = spec["pos"]
    name_iterator = make_names(spec)
    outcome = "done"
    session_pool = SessionPool(MAX_THREADS)

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

        if status == "free":
            time.sleep(0.1)
            again = check(session, name, job["stop"], job)
            if again in ("taken", "blocked"):
                status = again
        return idx, name, status

    try:
        chunk_size = MAX_THREADS * 5
        with ThreadPoolExecutor(max_workers=MAX_THREADS) as executor:
            while not job["stop"].is_set():
                batch = []
                for _ in range(chunk_size):
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
                        spec["pos"] = idx + 1

                        if status == "stopped":
                            outcome = "stopped"
                            break
                        if status == "error":
                            job["errors"] += 1
                            job["delay"] = min(job["delay"] * 1.5 + 0.3, MAX_AUTO_DELAY)
                            job["stop"].wait(1.5)
                            if job["errors"] >= MAX_ERRORS:
                                outcome = "blocked"
                                break
                            continue
                        if status == "limited":
                            stats["limited"] += 1
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
    "<b>Бот для поиска ников в Roblox (ИИ версия Gemini)</b>\n\n"
    "/menu — главное меню\n"
    f"<code>/ai [число] [тема]</code> — сгенерировать через Gemini и проверить "
    f"(по умолчанию {AI_DEFAULT}, максимум {AI_MAX}). Пример: <code>/ai 1000 dark fantasy</code>\n"
    "<code>/rate ник</code> — оценить ник (грейд и редкость)\n"
    "<code>/name ник</code> — быстрая проверка ников\n"
    "/all4 /all5 — поиск по всем комбинациям\n"
    "/pretty 4 — красивый перебор\n"
    "<code>/variants слово</code> — варианты слова\n"
    "<code>/scan шаблон [кол-во]</code> — поиск по шаблону (? буква, # цифра)\n"
    "/status /stop /resume — управление задачами\n"
    "/found — список найденных, /export — файл\n"
    "/delay — пауза между пачками"
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
    topic = rest or "cyberpunk aesthetic"
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
    session = requests.Session()
    never = threading.Event()
    lines = []
    for name in names[:MAX_QUICK]:
        if not valid_format(name):
            lines.append(f"⚪ <code>{html.escape(name)}</code> — неверный формат")
            continue
        st = check(session, name, never)
        label = {
            "free": f"🟢 <code>{name}</code> — свободен · {rating_line(name)}",
            "taken": f"🔴 <code>{name}</code> — занят",
            "blocked": f"⛔ <code>{name}</code> — запрещен",
        }.get(st, f"⚠️ <code>{name}</code> — ошибка")
        lines.append(label)
        time.sleep(0.1)
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
        set_delay(DELAY + (0.1 if data == "dl:+" else -0.1))
        tg(bot.answer_callback_query, c.id, f"Пауза {DELAY:.2f}с")
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
        # Сброс старых подключений, чтобы избежать ошибки 409 Conflict
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
