#!/usr/bin/env python3
"""순대트럭 크롤러 V3

V2 대비 개선점
  1. 수집량: 검색어당 3개 → 전부(최대 ~30개) 사용, 키워드 확장, 시드 지역 46 → ~150개
  2. 스노볼: 수집된 글 제목에서 '○○동'·트럭 브랜드명을 자동 추출해 다음 라운드 검색어로 추가
  3. SQLite 캐시: 검색결과/본문 파싱결과를 저장 → 재실행 시 새 글만 가져옴, 중단 후 재개 가능
  4. 날짜: 실제 작성일 파싱(“10시간 전”, “2026. 9. 17.” 등), 1년 초과 글 제외, 신선도 계산을 하드코딩에서 날짜 기반으로 변경
  5. 배차표 파서: 문장형 오탐(“저녁엔 순대트럭 어떠실까요”) 제거, “월·목 : ○○”, 다음 줄 장소, 휴무 처리
  6. 중복 병합: 같은 전화번호 / 같은 (요일,장소) 2쌍 이상 / 같은 브랜드+3km 이내 → 한 트럭으로 합침
  7. 지역: 블로그 지도 주소로 권역 판별, 정밀좌표 없는 글은 동 단위 지오코딩(OSM Nominatim) 후 '대략 위치'로 명시
  8. 가짜 데이터 제거: 랜덤 별점/리뷰수 생성 삭제

사용법
  python3 crawler_v3.py                 # 기본 실행 (캐시 사용)
  python3 crawler_v3.py --max-queries 300 --rounds 1 --no-geocode   # 빠른 테스트
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import re
import sqlite3
import threading
import time
import zlib
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timedelta
from urllib.parse import quote

import requests
from bs4 import BeautifulSoup

from seed_areas import KNOWN_BRANDS, SEED_AREAS

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.path.join(BASE_DIR, "crawl_cache.db")
OUT_JSON = os.path.join(BASE_DIR, "nationwide_trucks.json")
OUT_STATS = os.path.join(BASE_DIR, "crawl_stats.json")

NOW = datetime.now()
MAX_AGE_DAYS = 365
FRESH_DAYS = 90

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) "
        "AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1"
    ),
    "Accept-Language": "ko-KR,ko;q=0.9",
}

SEED_KEYWORDS = ["{a} 순대트럭", "{a} 순대차", "{a} 순대트럭 요일"]
DONG_KEYWORDS = ["{a} 순대트럭"]
BRAND_KEYWORDS = ["{a} 트럭", "{a} 요일"]

# 제목에 있으면 제외 (V2의 "배차", "이사"는 '배차표', '이사 온 동네' 같은 정상 글까지 걸러서 제거)
TITLE_SPAM = [
    "케이터링", "연예인", "서포트", "커피차", "기업행사", "학교행사", "용달", "화물",
    "전국배차", "고물상", "폐기물", "순대국", "순댓국", "국밥", "곰탕", "축제", "가볼만한곳",
    "중고트럭", "특장차", "렌탈", "대여", "분양", "창업", "가맹", "매매", "부동산",
]
TRUCK_TITLE_RE = re.compile(r"트럭|순대차|순대\s?차|푸드트럭|순대아저씨|이동식")
TRUCK_TERMS = ["순대트럭", "순대차", "순대 트럭", "순대 차", "푸드트럭", "트럭", "순대아저씨"]

GENERIC_SOONDAE = {
    "찰순대", "김치순대", "모듬순대", "모둠순대", "찹쌀순대", "전통순대", "토종순대", "병천순대",
    "백암순대", "아바이순대", "매운순대", "야채순대", "고기순대", "치즈순대", "삼겹순대", "카레순대",
    "트럭순대", "동네순대", "맛집순대", "옛날순대", "수제순대", "순대", "푸드트럭순대", "내장순대",
    "가성비순대", "포장순대", "인생순대맛집", "곱창순대", "두부순대", "땡초순대", "삼색순대", "정통순대",
    "시골순대", "오징어순대", "피순대", "막창순대", "당면순대", "왕순대", "꼬마순대", "순대순대",
}
# 지명+순대(광주순대, 부천순대…)는 브랜드가 아니라 지역 표현 → 시드 지역명·광역 지명으로 차단
PLACE_STEMS = {
    "서울", "부산", "대구", "인천", "광주", "대전", "울산", "세종", "제주", "경기", "강원", "충청", "충북", "충남",
    "전북", "전남", "경북", "경남", "수원", "성남", "용인", "고양", "부천", "안산", "안양", "남양주", "화성", "평택",
    "의정부", "시흥", "파주", "김포", "광명", "군포", "하남", "오산", "이천", "안성", "양주", "구리", "포천", "천안",
    "아산", "청주", "충주", "전주", "익산", "군산", "순천", "여수", "광양", "목포", "나주", "포항", "구미", "경산",
    "경주", "안동", "창원", "김해", "양산", "진주", "거제", "춘천", "원주", "강릉", "속초", "서귀포", "동탄", "일산",
    "분당", "송도", "청라", "검단", "세종시", "병천", "백암", "용인백암", "아바이", "속초아바이",
}
BRAND_ALIASES = {"그놈순대": "그놈의순대", "오늘순대": "오늘순대어때", "백암알천순대": "알천순대",
                 "옛날가마솥순대": "가마솥순대", "인생순대푸드트럭": "인생순대"}
# 제목에 트럭 표현 없이 이런 단어가 있으면 '가게(식당)' 글로 판단
RESTAURANT_TITLE_RE = re.compile(r"본점|직영점|[가-힣]{1,6}점(?:\s|$|,|\)|\]|\|)|정식|수육|웨이팅|오픈런|블루리본|순대실록|룸|단체석|주차")
STRONG_TRUCK_TERMS = ["순대트럭", "순대차", "순대 트럭", "순대 차", "푸드트럭", "순대아저씨", "트럭에서", "트럭이"]
DONG_STOP = {
    "이동", "운동", "행동", "자동", "공동", "활동", "감동", "출동", "작동", "변동", "가동", "진동",
    "충동", "노동", "아동", "기동", "유동", "연동", "수동", "파동", "거동", "합동", "협동", "율동",
    "부동", "생동", "선동", "폭동", "난동", "푸드동", "트럭동", "순대동", "그동", "이번동", "저번동",
}

REGION_BY_ADDR = [
    ("서울", "서울"), ("경기", "경기"), ("인천", "인천"), ("대전", "대전/세종"), ("세종", "대전/세종"),
    ("충청", "충청"), ("충북", "충청"), ("충남", "충청"), ("전북", "전북"), ("전라북", "전북"),
    ("광주", "광주/전남"), ("전남", "광주/전남"), ("전라남", "광주/전남"), ("대구", "대구/경북"),
    ("경북", "대구/경북"), ("경상북", "대구/경북"), ("부산", "부산/울산/경남"), ("울산", "부산/울산/경남"),
    ("경남", "부산/울산/경남"), ("경상남", "부산/울산/경남"), ("강원", "강원"), ("제주", "제주"),
]

DAY_CH = "월화수목금토일"
DAY_FULL = [d + "요일" for d in DAY_CH]


# ─────────────────────────────────────────────── 저장소
class Store:
    def __init__(self, path: str):
        self.conn = sqlite3.connect(path, check_same_thread=False)
        self.lock = threading.Lock()
        with self.lock:
            self.conn.executescript(
                """
                CREATE TABLE IF NOT EXISTS search_cache(query TEXT PRIMARY KEY, fetched_at TEXT, results TEXT);
                CREATE TABLE IF NOT EXISTS posts(url TEXT PRIMARY KEY, fetched_at TEXT, status TEXT, data TEXT);
                CREATE TABLE IF NOT EXISTS geocode(key TEXT PRIMARY KEY, lat REAL, lng REAL);
                """
            )
            self.conn.commit()
            self._migrate()

    def get_search(self, query: str, ttl_days: float):
        with self.lock:
            row = self.conn.execute(
                "SELECT fetched_at, results FROM search_cache WHERE query=?", (query,)
            ).fetchone()
        if not row:
            return None
        if datetime.fromisoformat(row[0]) < NOW - timedelta(days=ttl_days):
            return None
        return json.loads(row[1])

    def put_search(self, query: str, results: list):
        with self.lock:
            self.conn.execute(
                "INSERT OR REPLACE INTO search_cache VALUES (?,?,?)",
                (query, datetime.now().isoformat(), json.dumps(results, ensure_ascii=False)),
            )
            self.conn.commit()

    def _migrate(self):
        cols = {r[1] for r in self.conn.execute("PRAGMA table_info(posts)")}
        if "html" not in cols:  # V3.1: 원본 HTML 보관 → 파서 수정 시 재크롤링 없이 재분석
            self.conn.execute("ALTER TABLE posts ADD COLUMN html BLOB")
            self.conn.commit()

    def get_post(self, url: str):
        with self.lock:
            row = self.conn.execute(
                "SELECT status, data, html IS NOT NULL FROM posts WHERE url=?", (url,)
            ).fetchone()
        if not row:
            return None
        return row[0], (json.loads(row[1]) if row[1] else None), bool(row[2])

    def put_post(self, url: str, status: str, data: dict | None, html: str | None = None):
        blob = zlib.compress(html.encode("utf-8"), 6) if html else None
        with self.lock:
            self.conn.execute(
                "INSERT OR REPLACE INTO posts(url, fetched_at, status, data, html) VALUES (?,?,?,?,?)",
                (url, datetime.now().isoformat(), status,
                 json.dumps(data, ensure_ascii=False) if data else None, blob),
            )
            self.conn.commit()

    def update_parse(self, url: str, status: str, data: dict | None):
        with self.lock:
            self.conn.execute("UPDATE posts SET status=?, data=? WHERE url=?",
                              (status, json.dumps(data, ensure_ascii=False) if data else None, url))
            self.conn.commit()

    def iter_html(self):
        with self.lock:
            rows = self.conn.execute("SELECT url, html FROM posts WHERE html IS NOT NULL").fetchall()
        for url, blob in rows:
            yield url, zlib.decompress(blob).decode("utf-8")

    def get_geo(self, key: str):
        with self.lock:
            row = self.conn.execute("SELECT lat, lng FROM geocode WHERE key=?", (key,)).fetchone()
        return row  # (lat, lng) | (None, None) | None

    def put_geo(self, key: str, lat, lng):
        with self.lock:
            self.conn.execute("INSERT OR REPLACE INTO geocode VALUES (?,?,?)", (key, lat, lng))
            self.conn.commit()


# ─────────────────────────────────────────────── HTTP
class Fetcher:
    """모든 스레드가 공유하는 요청 간격(적응형).

    V3 전체 실행에서 3,701건 중 509건(14%)이 차단됨 → 스레드별 랜덤 지연 대신
    전역 간격을 두고, 차단되면 간격을 늘리고 45초 쉬었다가, 정상 응답이 이어지면 천천히 원래 속도로 복귀.
    """

    def __init__(self, base_interval: float = 0.7, max_interval: float = 6.0):
        self.base = self.interval = base_interval
        self.max_interval = max_interval
        self.local = threading.local()
        self.lock = threading.Lock()
        self.next_at = 0.0
        self.cool_until = 0.0
        self.blocked = 0
        self.requests = 0

    def _session(self):
        if not hasattr(self.local, "s"):
            self.local.s = requests.Session()
            self.local.s.headers.update(HEADERS)
        return self.local.s

    def _wait_turn(self):
        with self.lock:
            start = max(time.monotonic(), self.next_at, self.cool_until)
            self.next_at = start + self.interval * random.uniform(0.8, 1.3)
        time.sleep(max(0.0, start - time.monotonic()))

    def _on_block(self):
        with self.lock:
            self.blocked += 1
            self.interval = min(self.interval * 1.6, self.max_interval)
            self.cool_until = max(self.cool_until, time.monotonic() + 45)
            print(f"    ! 차단 감지 → 45초 휴식, 요청 간격 {self.interval:.1f}s", flush=True)

    def _on_ok(self):
        with self.lock:
            self.interval = max(self.base, self.interval * 0.97)

    def get(self, url: str) -> str | None:
        for attempt in range(4):
            self._wait_turn()
            try:
                r = self._session().get(url, timeout=12)
            except requests.RequestException:
                time.sleep(2 * (attempt + 1))
                continue
            with self.lock:
                self.requests += 1
            if r.status_code in (403, 429) or "비정상적인" in r.text[:3000]:
                self._on_block()
                continue
            self._on_ok()
            return r.text if r.status_code == 200 else None
        return None


# ─────────────────────────────────────────────── 파싱 유틸
def parse_post_date(raw: str) -> datetime | None:
    raw = raw or ""
    m = re.search(r"(\d{4})\.\s*(\d{1,2})\.\s*(\d{1,2})", raw)
    if m:
        try:
            return datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)))
        except ValueError:
            return None
    if re.search(r"(분|시간)\s*전|방금", raw):
        return NOW
    if "어제" in raw:
        return NOW - timedelta(days=1)
    m = re.search(r"(\d+)\s*일\s*전", raw)
    if m:
        return NOW - timedelta(days=int(m.group(1)))
    return None


def region_from_address(addr: str) -> str | None:
    if not addr:
        return None
    first = addr.split()[0]
    for prefix, region in REGION_BY_ADDR:
        if first.startswith(prefix):
            return region
    return None


def sub_area_from_address(addr: str) -> str:
    toks = [t for t in addr.split()[1:] if re.fullmatch(r"[가-힣]+(시|군|구|동|읍|면)", t)]
    return " ".join(toks[:2])


def in_korea(lat: float, lng: float) -> bool:
    return 33.0 <= lat <= 38.7 and 124.5 <= lng <= 131.0


def haversine_km(a, b) -> float:
    lat1, lng1, lat2, lng2 = map(math.radians, (a[0], a[1], b[0], b[1]))
    h = math.sin((lat2 - lat1) / 2) ** 2 + math.cos(lat1) * math.cos(lat2) * math.sin((lng2 - lng1) / 2) ** 2
    return 6371 * 2 * math.asin(math.sqrt(h))


def is_title_spam(title: str) -> bool:
    return any(k in title for k in TITLE_SPAM)


_BULLET = r"(?:[-•▪·✓✔☑📌🚚📍▶►*]+\s*)?"
_LINE_RE = re.compile(
    rf"^{_BULLET}((?:[{DAY_CH}](?:요일)?\s*[,/&·]\s*)*[{DAY_CH}])(?:요일)?(?:은|엔|에는)?\s*(?:[:：\-|]\s*|\s+)(.+)$"
)
_ONLY_DAY_RE = re.compile(rf"^{_BULLET}([{DAY_CH}])(?:요일)?\s*[:：]?$")
_SENTENCE = re.compile(r"(먹었|먹어|갔|왔어|오셨|있어요|있네|같아|니다|네요|어요|아요|는데|했|해요|ㅋ|ㅎ|ㅠ|\?|!|어떠|더라)")
_PLACE_HINT = re.compile(
    r"(아파트|단지|역|마트|앞|정문|후문|사거리|농협|상가|공원|학교|휴무|동|리|점|타운|빌|캐슬|자이|푸르지오|래미안|"
    r"힐스|더샵|편한세상|아이파크|센트럴|파크|시장|은행|우체국|마을|주공|휴먼시아|하이츠|맨션|[A-Za-z])"
)


def _days_in(s: str) -> list[str]:
    return re.findall(rf"[{DAY_CH}]", s.replace("요일", ""))


def _clean_value(v: str) -> str | None:
    v = v.replace("\u200b", "").strip(" :：-|,.!~")
    v = re.sub(r"\s+", " ", v)
    v = re.sub(r"^(그리고|그리고는|또는|또|및|그다음|다음은)\s*", "", v)
    if re.search(r"휴무|쉬는\s?날|쉽니다|쉬어요|안\s?나와", v) and len(v) <= 12:
        return "휴무"
    if not (2 <= len(v) <= 45):
        return None
    if re.match(r"^\d{1,2}(:\d{2}|시)", v):  # "13시~21시 (재료 소진시...)" 처럼 시간으로 시작
        return None
    if re.match(rf"^[{DAY_CH}](요일)?(\s|$|\d|~|,|·)", v):  # "월 ~ 금 15:30" 같은 범위 표현
        return None
    if re.fullmatch(r"[\d:~\s\-시분오후전밤()]+", v):  # 시간만 있는 줄
        return None
    if _SENTENCE.search(v):
        return None
    return v


def extract_schedule(paragraphs: list[str], full_text: str) -> dict:
    entries: dict[str, str] = {}
    for i, raw in enumerate(paragraphs):
        line = raw.replace("\u200b", "").strip()
        if len(line) > 70:
            continue
        m = _LINE_RE.match(line)
        if m:
            val = _clean_value(m.group(2))
            if val:
                for d in _days_in(m.group(1)):
                    entries.setdefault(d + "요일", val)
            continue
        m2 = _ONLY_DAY_RE.match(line)
        if m2 and i + 1 < len(paragraphs):
            val = _clean_value(paragraphs[i + 1])
            if val:
                entries.setdefault(m2.group(1) + "요일", val)

    # 한 요일만 잡혔으면 장소처럼 보일 때만 인정 (문장 오탐 방지)
    if len(entries) == 1:
        (d, v), = entries.items()
        if not _PLACE_HINT.search(v):
            entries = {}

    # "매주 수요일마다 금강아파트 앞" 같은 문장형
    for m3 in re.finditer(
        rf"매주\s*([{DAY_CH}](?:요일)?(?:\s*[,·]\s*[{DAY_CH}](?:요일)?)*)\s*(?:마다\s*)?"
        r"([가-힣0-9]{2,15}(?:\s?[가-힣0-9]{1,10})?(?:아파트|역|마트|단지|정문|후문|앞|사거리|우체국|학교))",
        full_text,
    ):
        for d in _days_in(m3.group(1)):
            entries.setdefault(d + "요일", m3.group(2).strip())

    return {d: entries[d] for d in DAY_FULL if d in entries}


def extract_mention_days(text: str) -> list[str]:
    days = set()
    for m in re.finditer(
        rf"매주\s*([{DAY_CH}])|([{DAY_CH}])요일\s*마다|([{DAY_CH}])요일(?:에|엔|은|만)?\s*(?:오|와|출몰|영업|장사)", text
    ):
        days.add((m.group(1) or m.group(2) or m.group(3)) + "요일")
    return [d for d in DAY_FULL if d in days]


def brand_candidates(title: str) -> list[str]:
    compact = re.sub(r"\s+", "", title)
    out = []
    for b in KNOWN_BRANDS:
        if b in compact:
            out.append(b)
    for tok in re.split(r"[^가-힣]+", title):
        m = re.match(r"^([가-힣]{2,4}?순대)", tok)
        if not m:
            continue
        b = m.group(1)
        stem = b[:-2]
        if (b in GENERIC_SOONDAE or stem in PLACE_STEMS or re.search(r"(동|역|구|시|군|읍)$", stem)
                or stem[-1] in "본은는던한운된" or stem in ("내돈내산", "맛집", "트럭", "푸드트럭", "전문", "우리", "동네")):
            continue
        out.append(b)
    out = [BRAND_ALIASES.get(b, b) for b in out]
    # '오늘순대'처럼 더 긴 브랜드의 앞부분이면 제거
    out = [b for b in out if not any(o != b and o.startswith(b) for o in out)]
    return list(dict.fromkeys(out))


def dong_candidates(title: str) -> list[str]:
    out = []
    for tok in re.split(r"[^가-힣]+", title):
        m = re.match(r"^([가-힣]{2,4}동)", tok)
        if m and m.group(1) not in DONG_STOP:
            out.append(m.group(1))
    return list(dict.fromkeys(out))


def parse_post(html: str, search_title: str) -> tuple[str, dict | None]:
    soup = BeautifulSoup(html, "lxml")
    og = soup.select_one("meta[property='og:title']")
    title = (og.get("content") if og else "") or search_title
    container = soup.select_one(".se-main-container") or soup.select_one("#viewTypeSelector")
    if not container:
        return "no_body", None
    if is_title_spam(title):
        return "spam", None

    paragraphs = [p.get_text(" ", strip=True) for p in container.select(".se-text-paragraph, tr, p")]
    paragraphs = [p for p in paragraphs if p]
    body = "\n".join(paragraphs)
    full = title + "\n" + body
    if "순대" not in full or not any(t in full for t in TRUCK_TERMS):
        return "irrelevant", None
    if not TRUCK_TITLE_RE.search(title):
        strong = sum(body.count(t) for t in STRONG_TRUCK_TERMS)
        if strong < 2 or RESTAURANT_TITLE_RE.search(title):
            return "restaurant", None

    date_el = soup.select_one(".se_publishDate") or soup.select_one(".blog_date") or soup.select_one("p.date")
    posted = parse_post_date(date_el.get_text(strip=True) if date_el else "")
    if posted and (NOW - posted).days > MAX_AGE_DAYS:
        return "old", None

    place = None
    for el in soup.select("[data-linkdata]"):
        raw = el.get("data-linkdata", "")
        if "latitude" not in raw:
            continue
        try:
            ld = json.loads(raw)
            lat, lng = float(ld["latitude"]), float(ld["longitude"])
        except (ValueError, KeyError, TypeError):
            continue
        if in_korea(lat, lng):
            place = {"name": ld.get("name", ""), "address": ld.get("address", ""), "lat": lat, "lng": lng}
            break

    schedule = extract_schedule(paragraphs, full)
    sched_days = [d for d, v in schedule.items() if "휴무" not in v]
    days = sched_days or extract_mention_days(full)

    locations = []
    if place and place["name"]:
        locations.append(place["name"])
    for loc in re.findall(
        r"([가-힣0-9]{2,12}(?:아파트|단지|역|사거리|초등학교|우체국|마트|농협|더샵|자이|푸르지오|래미안|롯데캐슬|"
        r"한신더휴|휴먼시아|주공)\s*(?:[0-9]+단지|[0-9]+차|정문|후문|앞)?)",
        full,
    ):
        loc = re.sub(r"\s+", " ", loc).strip()
        if loc not in locations:
            locations.append(loc)
        if len(locations) >= 5:
            break

    hours = re.findall(
        r"(\d{1,2}:\d{2}\s*[~\-]\s*\d{1,2}:\d{2}|오후\s*\d{1,2}시\s*(?:\d{1,2}분)?\s*[~\-]\s*(?:오후\s*|밤\s*)?\d{1,2}시)", full
    )
    images = [
        img.get("data-lazy-src") or img.get("src") or ""
        for img in container.select("img")
    ]
    images = [s for s in images if "pstatic.net" in s and "sticker" not in s and "profile" not in s]

    return "ok", {
        "title": title.strip(),
        "posted": posted.date().isoformat() if posted else None,
        "place": place,
        "schedule": schedule,
        "days": days,
        "days_source": "schedule" if sched_days else ("mention" if days else "none"),
        "locations": locations,
        "phones": sorted({re.sub(r"\D", "", p) for p in re.findall(r"010[-.\s]?\d{4}[-.\s]?\d{4}", full)}),
        "hours": hours[0] if hours else "",
        "menus": sorted(set(re.findall(
            r"(찰순대|김치순대|모듬순대|모둠순대|삼겹순대|치즈순대|매운순대|카레순대|곱창|전기구이\s*통닭|"
            r"전통순대|토종순대|병천순대|찹쌀순대|아바이순대|내장|오징어순대)", full))),
        "prices": sorted(set(re.findall(r"(\d{1,2},\d{3}원|\d{1,2}천\s?원)", full)))[:6],
        "payments": sorted({re.sub(r"\s", "", p) for p in re.findall(
            r"(계좌\s*이체|현금|카드\s*가능|카드결제|지역화폐|온누리|제로페이)", full)}),
        "image_count": len(images),
        "brands": brand_candidates(title),
        "dongs": dong_candidates(title),
    }


# ─────────────────────────────────────────────── 크롤 단계
class Crawler:
    def __init__(self, store: Store, fetcher: Fetcher, workers: int, search_ttl: float):
        self.store, self.fetcher = store, fetcher
        self.workers, self.search_ttl = workers, search_ttl
        self.url_target: dict[str, dict] = {}
        self.url_title: dict[str, str] = {}
        self.records: dict[str, dict] = {}
        self.seen_posts: set[str] = set()
        self.done_queries: set[str] = set()
        self.stats = Counter()

    def search(self, query: str) -> list[dict]:
        cached = self.store.get_search(query, self.search_ttl)
        if cached is not None:
            self.stats["search_cache_hit"] += 1
            return cached
        url = (f"https://m.search.naver.com/search.naver?ssc=tab.m_blog.all&query={quote(query)}"
               f"&sm=mtb_opt&nso=so%3Ar%2Cp%3A1y")
        html = self.fetcher.get(url)
        if html is None:
            self.stats["search_fail"] += 1
            return []
        soup = BeautifulSoup(html, "lxml")
        best: dict[str, str] = {}
        for a in soup.select("a[href*='m.blog.naver.com']"):
            m = re.match(r"https?://m\.blog\.naver\.com/([^/?#]+)/(\d+)", a.get("href", ""))
            if not m:
                continue
            u = f"https://m.blog.naver.com/{m.group(1)}/{m.group(2)}"
            t = a.get_text(" ", strip=True)
            if "순대" in t and 6 <= len(t) <= 120 and ("순대" not in best.get(u, "") or len(t) < len(best[u])):
                best[u] = t
            else:
                best.setdefault(u, "")
        results = [{"url": u, "title": t} for u, t in best.items()]
        self.store.put_search(query, results)
        self.stats["search_fetched"] += 1
        return results

    def run_queries(self, jobs: list[tuple[str, dict]]):
        jobs = [(q, t) for q, t in jobs if q not in self.done_queries]
        for q, _ in jobs:
            self.done_queries.add(q)
        with ThreadPoolExecutor(self.workers) as ex:
            futs = {ex.submit(self.search, q): t for q, t in jobs}
            for f in as_completed(futs):
                target = futs[f]
                for r in f.result():
                    if "순대" not in r["title"] or is_title_spam(r["title"]):
                        continue
                    self.url_target.setdefault(r["url"], target)
                    self.url_title.setdefault(r["url"], r["title"])
        return len(jobs)

    def _fetch_post(self, url: str):
        cached = self.store.get_post(url)
        if cached:
            self.stats["post_cache_hit"] += 1
            return url, cached[0], cached[1]
        html = self.fetcher.get(url)
        if html is None:
            return url, "fetch_fail", None  # 캐시하지 않음 → 다음 실행 때 재시도
        status, data = parse_post(html, self.url_title.get(url, ""))
        self.store.put_post(url, status, data)
        self.stats["post_fetched"] += 1
        return url, status, data

    def fetch_posts(self):
        todo = [u for u in self.url_target if u not in self.seen_posts]
        with ThreadPoolExecutor(self.workers + 2) as ex:
            for i, f in enumerate(as_completed([ex.submit(self._fetch_post, u) for u in todo]), 1):
                url, status, data = f.result()
                self.seen_posts.add(url)
                self.stats[f"status_{status}"] += 1
                if status == "ok" and data:
                    self.records[url] = {**data, "url": url, "target": self.url_target[url]}
                if i % 200 == 0:
                    print(f"    · 본문 {i}/{len(todo)} 처리, 유효 {len(self.records)}개", flush=True)
        return len(todo)


def snowball_jobs(crawler: Crawler, max_new: int) -> list[tuple[str, dict]]:
    dong_cnt, dong_target = Counter(), {}
    brand_cnt, brand_target = Counter(), {}
    for r in crawler.records.values():
        if r["target"].get("region") is None:
            continue  # 위치 단서 없는 글(브랜드 검색 유입)에서는 확장하지 않음
        for d in r.get("dongs", []):
            dong_cnt[d] += 1
            dong_target.setdefault(d, r["target"])
        for b in (r.get("brands", []) if TRUCK_TITLE_RE.search(r["title"]) else []):
            brand_cnt[b] += 1
            brand_target.setdefault(b, r["target"])

    jobs = []
    for b, c in brand_cnt.most_common():
        if c >= 2 or b in KNOWN_BRANDS:
            for kw in BRAND_KEYWORDS:
                # 브랜드는 체인일 수 있어 지역을 확정하지 않음 → 지도 주소(정밀좌표)가 있는 글만 최종 반영
                jobs.append((kw.format(a=b), {"kind": "brand", "brand": b, "region": None,
                                               "area": b, "lat": None, "lng": None}))
    for d, _ in dong_cnt.most_common():
        parent = dong_target[d]
        for kw in DONG_KEYWORDS:
            jobs.append((kw.format(a=d), {"kind": "dong", "region": parent["region"], "area": d,
                                          "parent_area": parent["area"], "lat": parent["lat"], "lng": parent["lng"]}))
    jobs = [(q, t) for q, t in jobs if q not in crawler.done_queries]
    return jobs[:max_new]


# ─────────────────────────────────────────────── 지오코딩 (정밀좌표 없는 글 → 동 중심)
def geocode_dong(store: Store, dong: str, parent: str) -> tuple[float, float] | None:
    key = f"{dong}|{parent}"
    cached = store.get_geo(key)
    if cached is not None:
        return (cached[0], cached[1]) if cached[0] is not None else None
    time.sleep(1.1)  # Nominatim 이용정책: 초당 1회 이하
    try:
        r = requests.get(
            "https://nominatim.openstreetmap.org/search",
            params={"q": f"{dong} {parent}", "format": "json", "limit": 1, "countrycodes": "kr"},
            headers={"User-Agent": "soondae-radar-prototype/0.3 (local research)"},
            timeout=10,
        )
        hits = r.json() if r.status_code == 200 else []
    except (requests.RequestException, ValueError):
        return None
    if hits:
        lat, lng = float(hits[0]["lat"]), float(hits[0]["lon"])
        store.put_geo(key, lat, lng)
        return lat, lng
    store.put_geo(key, None, None)
    return None


# ─────────────────────────────────────────────── 중복 병합
class DSU:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a, b):
        self.p[self.find(a)] = self.find(b)


def _norm_loc(v: str) -> str:
    return re.sub(r"[^가-힣A-Za-z0-9]", "", v)[:6]


def resolve_entities(recs: list[dict], known_brands: set[str]) -> list[list[dict]]:
    n = len(recs)
    dsu = DSU(n)
    by_phone, by_pair, by_brand = defaultdict(list), defaultdict(list), defaultdict(list)
    for i, r in enumerate(recs):
        for p in r["phones"]:
            by_phone[p].append(i)
        for d, v in r["schedule"].items():
            if "휴무" not in v:
                by_pair[(d, _norm_loc(v))].append(i)
        if r.get("brand"):
            by_brand[r["brand"]].append(i)

    for idxs in by_phone.values():
        for j in idxs[1:]:
            dsu.union(idxs[0], j)

    pair_hits = Counter()
    for idxs in by_pair.values():
        for a in range(len(idxs)):
            for b in range(a + 1, len(idxs)):
                pair_hits[(idxs[a], idxs[b])] += 1
    for (a, b), c in pair_hits.items():
        if c >= 2:
            dsu.union(a, b)

    for idxs in by_brand.values():
        for a in range(len(idxs)):
            for b in range(a + 1, len(idxs)):
                ra, rb = recs[idxs[a]], recs[idxs[b]]
                if haversine_km((ra["lat"], ra["lng"]), (rb["lat"], rb["lng"])) <= 3.0:
                    dsu.union(idxs[a], idxs[b])

    groups = defaultdict(list)
    for i in range(n):
        groups[dsu.find(i)].append(recs[i])
    return list(groups.values())


def merge_group(group: list[dict]) -> dict:
    group = sorted(group, key=lambda r: r["posted"] or "0000", reverse=True)  # 최신 글 우선
    newest = group[0]
    schedule = {}
    for r in group:
        for d, v in r["schedule"].items():
            schedule.setdefault(d, v)
    schedule = {d: schedule[d] for d in DAY_FULL if d in schedule}
    days = [d for d in DAY_FULL if any(d in r["days"] for r in group)]
    exact = next((r for r in group if r["coord_precision"] == "exact"), None)
    loc_src = exact or newest
    brands = Counter(r["brand"] for r in group if r.get("brand"))
    brand = brands.most_common(1)[0][0] if brands else None

    def union(key, limit):
        out = []
        for r in group:
            for x in r[key]:
                if x not in out:
                    out.append(x)
        return out[:limit]

    name = brand or re.sub(r"\s+", " ", re.sub(
        r"내돈내산|솔직|포장|후기|총정리|요일별|위치|가격|영업시간|및|\||\[.*?\]", " ", newest["title"])).strip()[:26]
    last_seen = newest["posted"]
    days_since = (NOW.date() - datetime.fromisoformat(last_seen).date()).days if last_seen else None
    phones = union("phones", 3)
    return {
        "id": hashlib.md5(min(r["url"] for r in group).encode()).hexdigest()[:10],
        "truck_name": name or f"{loc_src['sub_region']} 순대트럭",
        "brand": brand,
        "region": loc_src["region"],
        "sub_region": loc_src["sub_region"],
        "last_seen": last_seen,
        "days_since": days_since,
        "freshness_level": "high" if days_since is not None and days_since <= FRESH_DAYS else "medium",
        "days": days,
        "days_source": "schedule" if schedule else ("mention" if days else "none"),
        "weekly_schedule": schedule,
        "locations": union("locations", 5),
        "exact_address": exact["place"]["address"] if exact else "",
        "coord_precision": loc_src["coord_precision"],
        "lat": loc_src["lat"],
        "lng": loc_src["lng"],
        "phones": [f"{p[:3]}-{p[3:7]}-{p[7:]}" for p in phones],
        "hours": next((r["hours"] for r in group if r["hours"]), ""),
        "menus": union("menus", 6),
        "prices": union("prices", 5),
        "payments": union("payments", 4),
        "image_count": sum(r["image_count"] for r in group),
        "source_count": len(group),
        "sources": [{"url": r["url"], "title": r["title"], "posted": r["posted"]} for r in group[:8]],
    }


def build(crawler: Crawler, store: Store, do_geocode: bool, brand_set: set[str]) -> list[dict]:
    recs = []
    geo_calls = 0
    for r in crawler.records.values():
        t = r["target"]
        place = r["place"]
        region = region_from_address(place["address"]) if place else None
        region = region or t.get("region")
        if not region:
            continue  # 브랜드 검색으로만 들어왔고 위치 단서가 없는 글
        r = dict(r)
        r["brand"] = next((b for b in r["brands"] if b in brand_set), None)
        r["region"] = region
        if place:
            r.update(lat=place["lat"], lng=place["lng"], coord_precision="exact",
                     sub_region=sub_area_from_address(place["address"]) or t.get("area", ""))
        else:
            lat, lng, prec = t.get("lat"), t.get("lng"), "area"
            if t.get("kind") == "dong" and do_geocode:
                hit = geocode_dong(store, t["area"], t.get("parent_area", ""))
                geo_calls += 1
                if hit and haversine_km(hit, (t["lat"], t["lng"])) < 40:
                    lat, lng, prec = hit[0], hit[1], "dong"
            if lat is None:
                continue
            rnd = random.Random(r["url"])  # 같은 글은 항상 같은 위치 (겹침 방지용 소폭 이동)
            spread = 0.003 if prec == "dong" else 0.01
            r.update(lat=round(lat + rnd.uniform(-spread, spread), 5),
                     lng=round(lng + rnd.uniform(-spread, spread), 5),
                     coord_precision=prec,
                     sub_region=t["area"] if t.get("kind") != "dong" else f"{t.get('parent_area', '')} {t['area']}".strip())
        recs.append(r)

    trucks = [merge_group(g) for g in resolve_entities(recs, brand_set)]
    trucks.sort(key=lambda x: (x["last_seen"] or "0000", x["source_count"]), reverse=True)
    crawler.stats["geocode_lookups"] = geo_calls
    crawler.stats["posts_before_merge"] = len(recs)
    return trucks


# ─────────────────────────────────────────────── main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-queries", type=int, default=900, help="전체 검색 횟수 상한")
    ap.add_argument("--rounds", type=int, default=2, help="스노볼 라운드 수")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--search-ttl", type=float, default=3.0, help="검색결과 캐시 유효기간(일)")
    ap.add_argument("--no-geocode", action="store_true")
    args = ap.parse_args()

    t0 = time.time()
    store, fetcher = Store(DB_PATH), Fetcher()
    crawler = Crawler(store, fetcher, args.workers, args.search_ttl)

    seed_jobs = []
    for region, area, lat, lng in SEED_AREAS:
        for kw in SEED_KEYWORDS:
            seed_jobs.append((kw.format(a=area), {"kind": "seed", "region": region, "area": area, "lat": lat, "lng": lng}))
    budget = args.max_queries

    print(f"[1] 시드 검색 {min(len(seed_jobs), budget)}건 (지역 {len(SEED_AREAS)}곳 × 키워드 {len(SEED_KEYWORDS)}개)")
    used = crawler.run_queries(seed_jobs[:budget])
    budget -= used
    print(f"    후보 글 {len(crawler.url_target)}개 → 본문 분석")
    crawler.fetch_posts()
    print(f"    유효 글 {len(crawler.records)}개")

    for rnd in range(1, args.rounds + 1):
        if budget <= 0:
            break
        jobs = snowball_jobs(crawler, budget)
        if not jobs:
            break
        print(f"[{rnd + 1}] 스노볼 라운드 {rnd}: 새 검색어 {len(jobs)}건 (동/브랜드 자동 추출)")
        budget -= crawler.run_queries(jobs)
        crawler.fetch_posts()
        print(f"    누적 후보 {len(crawler.url_target)}개 / 유효 글 {len(crawler.records)}개")

    brand_cnt = Counter(b for r in crawler.records.values() if TRUCK_TITLE_RE.search(r["title"]) for b in r["brands"])
    brand_set = set(KNOWN_BRANDS) | {b for b, c in brand_cnt.items() if c >= 2}

    print("[*] 위치 보정 · 중복 병합 · 내보내기")
    trucks = build(crawler, store, not args.no_geocode, brand_set)

    tmp = OUT_JSON + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(trucks, f, ensure_ascii=False, indent=1)
    os.replace(tmp, OUT_JSON)

    st = crawler.stats
    summary = {
        "generated_at": datetime.now().isoformat(timespec="seconds"),
        "elapsed_sec": round(time.time() - t0),
        "queries": len(crawler.done_queries),
        "search_fetched": st["search_fetched"], "search_cache_hit": st["search_cache_hit"],
        "search_fail": st["search_fail"],
        "candidate_posts": len(crawler.url_target),
        "post_status": {k[7:]: v for k, v in st.items() if k.startswith("status_")},
        "valid_posts": len(crawler.records),
        "posts_before_merge": st["posts_before_merge"],
        "trucks": len(trucks),
        "with_schedule": sum(1 for t in trucks if t["weekly_schedule"]),
        "with_days": sum(1 for t in trucks if t["days"]),
        "with_phone": sum(1 for t in trucks if t["phones"]),
        "coord_precision": dict(Counter(t["coord_precision"] for t in trucks)),
        "fresh_90d": sum(1 for t in trucks if t["freshness_level"] == "high"),
        "multi_source_trucks": sum(1 for t in trucks if t["source_count"] > 1),
        "by_region": dict(Counter(t["region"] for t in trucks).most_common()),
        "brands": sorted(brand_set),
        "http_requests": fetcher.requests, "blocked": fetcher.blocked,
        "geocode_lookups": st["geocode_lookups"],
    }
    with open(OUT_STATS, "w", encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=1)
    print(json.dumps(summary, ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
