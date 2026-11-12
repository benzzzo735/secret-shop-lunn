"""Ночной магазин в общежитии — два Telegram-бота в одном скрипте (aiogram 3 + SQLite).

1) Бот покупателя (BOT_TOKEN): каталог с описаниями и артикулами, корзина, заказ,
   кнопка «Я оплатил(а)», статус заказов (/myorders).
2) Бот продавца (SELLER_BOT_TOKEN): заказы, подтверждение оплаты, комната выдачи,
   склад, цены, описания, артикулы, добавление товаров.

Оба бота работают с одной базой shop.db. Есть категории, акции, промокоды, поиск, повтор заказа,
режим работы, бронь с автоотменой, массовая загрузка из CSV/XLSX и выпадающее меню команд. Заказы продавцу приходят во второго бота,
поэтому продавец должен один раз нажать /start в боте продавца.
"""
import asyncio
import csv
import html
import io
import json
import logging
import os
import random
import re
import socket
import sqlite3
import tempfile
import textwrap
import time
import zipfile
import zlib
from collections import Counter, deque
from contextlib import contextmanager
from datetime import datetime, timedelta
from urllib.parse import quote
from zoneinfo import ZoneInfo

from aiogram import BaseMiddleware, Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramRetryAfter
from aiogram.filters import Command, CommandStart
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BotCommand,
    BotCommandScopeChat,
    BotCommandScopeDefault,
    BufferedInputFile,
    ChatMemberUpdated,
    CallbackQuery,
    FSInputFile,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    MenuButtonCommands,
    Message,
)
from aiogram.utils.keyboard import InlineKeyboardBuilder
from dotenv import load_dotenv

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
load_dotenv(os.path.join(BASE_DIR, ".env"))

BOT_TOKEN = os.environ["BOT_TOKEN"]  # бот покупателя
SELLER_BOT_TOKEN = os.environ["SELLER_BOT_TOKEN"]  # бот продавца
ADMIN_ID = int(os.environ["ADMIN_ID"])  # Telegram ID продавца
PAYMENT_INFO = os.getenv("PAYMENT_INFO", "Реквизиты для перевода уточните у продавца.")
TZ = os.getenv("TIMEZONE", "Europe/Moscow")
# Магазин работает круглосуточно. OPEN_HOUR/CLOSE_HOUR нужны только статистике:
# так определяется «ночная смена» (по умолчанию 23:00 → 06:00).
OPEN_HOUR = int(os.getenv("OPEN_HOUR", "23"))
CLOSE_HOUR = int(os.getenv("CLOSE_HOUR", "6"))
# Ночная наценка: с SURCHARGE_FROM до SURCHARGE_TO (по умолчанию 02:00–06:00) цены +30%.
SURCHARGE_PERCENT = int(os.getenv("SURCHARGE_PERCENT", "30"))
SURCHARGE_FROM = int(os.getenv("SURCHARGE_FROM", "2"))
SURCHARGE_TO = int(os.getenv("SURCHARGE_TO", "6"))
# На хостингах данные переживают обновления только в особой папке (/data у FadeHost, /app/data у Bothost).
# Если она есть — бот сам кладёт туда базу и фото, даже если переменные DB_PATH/PHOTOS_DIR не заданы.
def _default_data_dir():
    for d in ("/data", "/app/data"):
        if os.path.isdir(d) and os.access(d, os.W_OK):
            return d
    return BASE_DIR


DATA_DIR = _default_data_dir()
PHOTOS_DIR = os.getenv("PHOTOS_DIR", os.path.join(DATA_DIR, "photos"))
DB_PATH = os.getenv("DB_PATH", os.path.join(DATA_DIR, "shop.db"))
# Режим работы: пусто = круглосуточно. Можно менять прямо из бота продавца: /hours 22:00 06:00
WORK_FROM = os.getenv("WORK_FROM", "")
WORK_TO = os.getenv("WORK_TO", "")
# Бронь: неоплаченный заказ переводом автоматически отменяется через столько минут (0 — не отменять)
RESERVE_MINUTES = int(os.getenv("RESERVE_MINUTES", "20"))
# Уведомлять продавца, когда остаток товара стал таким или меньше
LOW_STOCK = int(os.getenv("LOW_STOCK", "2"))
# Ежедневная резервная копия (база + фото) в личку продавцу; "off" — выключить
BACKUP_TIME = os.getenv("BACKUP_TIME", "04:00")
# Автоотчёт после ночной смены; по умолчанию через 10 минут после CLOSE_HOUR; "off" — выключить
REPORT_TIME = os.getenv("REPORT_TIME", f"{CLOSE_HOUR:02d}:10")
# Защита от спама: не больше RATE_LIMIT действий за RATE_WINDOW секунд, иначе пауза RATE_BLOCK секунд
RATE_LIMIT = int(os.getenv("RATE_LIMIT", "12"))
RATE_WINDOW = int(os.getenv("RATE_WINDOW", "10"))
RATE_BLOCK = int(os.getenv("RATE_BLOCK", "30"))
# Сколько незавершённых заказов может быть у одного покупателя одновременно
MAX_ACTIVE_ORDERS = int(os.getenv("MAX_ACTIVE_ORDERS", "3"))
# «Приведи друга»: скидка другу на первый заказ и награда пригласившему, ₽ (0 — выключить)
REF_FRIEND_AMOUNT = int(os.getenv("REF_FRIEND_AMOUNT", "30"))
REF_REWARD_AMOUNT = int(os.getenv("REF_REWARD_AMOUNT", "30"))
REF_MIN_TOTAL = int(os.getenv("REF_MIN_TOTAL", "100"))  # награда — когда заказ друга выдан и не меньше этой суммы
REF_MAX_REWARDS = int(os.getenv("REF_MAX_REWARDS", "5"))  # максимум наград одному человеку (0 — без лимита)
SUPPORT_MIN_GAP = int(os.getenv("SUPPORT_MIN_GAP", "10"))  # пауза между сообщениями в поддержку, сек

# Стартовый ассортимент для НОВОЙ базы: (название, цена, остаток, описание, закупка).
# Цены, остатки и закупку меняйте из бота продавца: /setprice, /setstock, /setcost, /setdesc.
SEED_PRODUCTS = [
    ("Добрый Кола без сахара 1,5 л", 150, 9,
     "Газированный напиток со вкусом колы, в котором вместо сахара используются "
     "подсластители, поэтому калорий в нём почти нет. Большая бутылка 1,5 л — хватит "
     "на компанию или на всю ночь. Лучше подавать хорошо охлаждённой.", 107.7),
    ("Роллтон Курица", 40, 5,
     "Лапша быстрого приготовления со вкусом курицы: в комплекте лапша и пакетик с приправой. "
     "Залейте кипятком, накройте на несколько минут — и горячий перекус готов. "
     "Быстро, сытно и недорого.", 21.9),
    ("Роллтон Говядина", 40, 5,
     "Лапша быстрого приготовления со вкусом говядины: в комплекте лапша и пакетик с приправой. "
     "Залейте кипятком, накройте на несколько минут — и горячий перекус готов. "
     "Более насыщенный, «мясной» вкус.", 21.9),
    ("MultiChips Сметана и лук", 60, 5,
     "Хрустящие картофельные чипсы со вкусом сметаны и лука. Классический мягкий "
     "кисло-сливочный вкус с луковой ноткой — под сериал или настолки.", 41),
    ("Lay's Краб 70 г", 125, 5,
     "Тонкие хрустящие картофельные чипсы Lay's со вкусом краба, пачка 70 г. "
     "Яркий пикантный вкус — один из самых популярных у Lay's.", 89.9),
    ("Lay's Сметана и лук 70 г", 125, 5,
     "Тонкие хрустящие картофельные чипсы Lay's со вкусом сметаны и лука, пачка 70 г. "
     "Мягкий сливочный вкус с луком — классика.", 89.9),
]
# Для уже существующей базы: описания и закупка подставятся по названию,
# если у товара они пустые (или это старое короткое описание из прошлой версии).
DEFAULT_DESCRIPTIONS = {n: d for n, _, _, d, _ in SEED_PRODUCTS}
DEFAULT_COSTS = {n: c for n, _, _, _, c in SEED_PRODUCTS}
for _d in (DEFAULT_DESCRIPTIONS, DEFAULT_COSTS):
    _d["Mega Chips Сметана и лук"] = _d["MultiChips Сметана и лук"]
# Категории для стартового ассортимента (дальше: /setcat id категория)
DEFAULT_CATEGORIES = {
    "Добрый Кола без сахара 1,5 л": "Напитки",
    "Роллтон Курица": "Лапша",
    "Роллтон Говядина": "Лапша",
    "MultiChips Сметана и лук": "Снеки",
    "Mega Chips Сметана и лук": "Снеки",
    "Lay's Краб 70 г": "Снеки",
    "Lay's Сметана и лук 70 г": "Снеки",
}
# Прежние короткие описания: их можно безопасно заменить на новые.
OLD_DESCRIPTIONS = {
    "Газированный напиток без сахара, 1,5 л. Лучше всего холодным.",
    "Лапша быстрого приготовления со вкусом курицы. Залить кипятком и подождать.",
    "Лапша быстрого приготовления со вкусом говядины. Залить кипятком и подождать.",
    "Картофельные чипсы со вкусом сметаны и лука.",
    "Картофельные чипсы Lay's со вкусом краба, 70 г.",
    "Картофельные чипсы Lay's со вкусом сметаны и лука, 70 г.",
}

PAY_LABELS = {"transfer": "перевод", "cash": "наличные"}
STATUS_LABELS = {"new": "принят", "ready": "собран", "done": "выдан", "cancelled": "отменён"}
STATUS_ICONS = {"new": "🆕", "ready": "📦", "done": "✅", "cancelled": "❌"}
ACTIVE_STATUSES = ("new", "ready")  # new — принят, ready — собран, комната указана
SKU_RE = re.compile(r"^[A-Za-zА-Яа-я0-9_-]{1,20}$")

# Объекты Bot создаются в main(); обработчики берут их отсюда.
bots = {}

customer_router = Router()
seller_router = Router()
guest_router = Router()
# Продавца пускаем только по ADMIN_ID, остальным отвечает guest_router.
seller_router.message.filter(F.from_user.id == ADMIN_ID)
seller_router.callback_query.filter(F.from_user.id == ADMIN_ID)


class AdminRoom(StatesGroup):
    room = State()


class Suggest(StatesGroup):
    text = State()


class PromoInput(StatesGroup):
    code = State()


class Support(StatesGroup):
    text = State()


class SupportReply(StatesGroup):
    text = State()


class Broadcast(StatesGroup):
    content = State()


# ═══ DB BEGIN ═══════════════════════ База данных ═══════════════════════
@contextmanager
def db():
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    try:
        yield conn
        conn.commit()
    finally:
        conn.close()


def ensure_column(c, table, column, ddl):
    cols = [r["name"] for r in c.execute(f"PRAGMA table_info({table})")]
    if column not in cols:
        c.execute(f"ALTER TABLE {table} ADD COLUMN {column} {ddl}")


def make_sku(c, pid):
    """Свободный артикул вида A001 для товара с данным id."""
    cand, n = f"A{pid:03d}", 0
    while c.execute(
        "SELECT 1 FROM products WHERE lower(sku)=lower(?) AND id<>?", (cand, pid)
    ).fetchone():
        n += 1
        cand = f"A{pid:03d}-{n}"
    return cand


def init_db():
    with db() as c:
        c.executescript(
            """
            CREATE TABLE IF NOT EXISTS products(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                price INTEGER NOT NULL,
                stock INTEGER NOT NULL DEFAULT 0,
                active INTEGER NOT NULL DEFAULT 1,
                sku TEXT,
                description TEXT NOT NULL DEFAULT '',
                cost REAL,
                photo TEXT,
                photo_fid TEXT
            );
            CREATE TABLE IF NOT EXISTS carts(
                user_id INTEGER NOT NULL,
                product_id INTEGER NOT NULL,
                qty INTEGER NOT NULL,
                PRIMARY KEY(user_id, product_id)
            );
            -- room = комната выдачи (пустая строка, пока продавец её не указал)
            -- pay_status: unpaid -> claimed (клиент нажал «Я оплатил») -> paid
            CREATE TABLE IF NOT EXISTS orders(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                username TEXT,
                full_name TEXT,
                room TEXT NOT NULL DEFAULT '',
                payment TEXT NOT NULL,
                total INTEGER NOT NULL,
                items_json TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'new',
                created_at TEXT NOT NULL,
                pay_status TEXT NOT NULL DEFAULT 'unpaid'
            );
            -- предложения покупателей; status: new / planned / done / rejected
            CREATE TABLE IF NOT EXISTS suggestions(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                username TEXT,
                full_name TEXT,
                text TEXT NOT NULL,
                status TEXT NOT NULL DEFAULT 'new',
                created_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS suggestion_votes(
                suggestion_id INTEGER NOT NULL,
                user_id INTEGER NOT NULL,
                PRIMARY KEY(suggestion_id, user_id)
            );
            CREATE TABLE IF NOT EXISTS settings(
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            );
            -- промокод: percent (скидка в %) ИЛИ amount (скидка в рублях); max_uses NULL = без лимита
            CREATE TABLE IF NOT EXISTS promocodes(
                code TEXT PRIMARY KEY,
                percent INTEGER NOT NULL DEFAULT 0,
                amount INTEGER NOT NULL DEFAULT 0,
                max_uses INTEGER,
                used INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS promo_uses(
                code TEXT NOT NULL,
                user_id INTEGER NOT NULL,
                order_id INTEGER NOT NULL
            );
            -- все, кто запускал бота покупателя
            CREATE TABLE IF NOT EXISTS users(
                user_id INTEGER PRIMARY KEY,
                username TEXT,
                full_name TEXT,
                first_seen TEXT NOT NULL,
                last_seen TEXT NOT NULL,
                subscribed INTEGER NOT NULL DEFAULT 1,   -- согласие на рассылку
                blocked INTEGER NOT NULL DEFAULT 0,      -- заблокировал бота
                referrer_id INTEGER,                     -- кто пригласил
                ref_rewarded INTEGER NOT NULL DEFAULT 0  -- пригласившему уже выдана награда
            );
            CREATE TABLE IF NOT EXISTS stock_subs(
                user_id INTEGER NOT NULL,
                product_id INTEGER NOT NULL,
                created_at TEXT NOT NULL,
                PRIMARY KEY(user_id, product_id)
            );
            CREATE TABLE IF NOT EXISTS tickets(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                username TEXT,
                full_name TEXT,
                order_id INTEGER,
                status TEXT NOT NULL DEFAULT 'open',
                created_at TEXT NOT NULL,
                updated_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS ticket_msgs(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                ticket_id INTEGER NOT NULL,
                from_seller INTEGER NOT NULL,
                text TEXT NOT NULL DEFAULT '',
                has_photo INTEGER NOT NULL DEFAULT 0,
                created_at TEXT NOT NULL
            );
            CREATE TABLE IF NOT EXISTS broadcasts(
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                created_at TEXT NOT NULL,
                audience TEXT NOT NULL,
                text TEXT NOT NULL,
                total INTEGER NOT NULL DEFAULT 0,
                sent INTEGER NOT NULL DEFAULT 0,
                failed INTEGER NOT NULL DEFAULT 0,
                has_photo INTEGER NOT NULL DEFAULT 0
            );
            CREATE TABLE IF NOT EXISTS cart_promos(
                user_id INTEGER PRIMARY KEY,
                code TEXT NOT NULL
            );
            """
        )
        # миграции для баз, созданных прошлыми версиями
        ensure_column(c, "products", "sku", "TEXT")
        ensure_column(c, "products", "description", "TEXT NOT NULL DEFAULT ''")
        ensure_column(c, "orders", "pay_status", "TEXT NOT NULL DEFAULT 'unpaid'")
        ensure_column(c, "products", "cost", "REAL")
        # photo — ссылка (http...) или имя файла в папке photos/;
        # photo_fid — кэш file_id фото в боте покупателя (file_id привязан к боту)
        ensure_column(c, "products", "photo", "TEXT")
        ensure_column(c, "products", "photo_fid", "TEXT")
        first_cat = "category" not in [r["name"] for r in c.execute("PRAGMA table_info(products)")]
        ensure_column(c, "products", "category", "TEXT NOT NULL DEFAULT ''")
        ensure_column(c, "products", "sale_price", "INTEGER")  # цена по акции (NULL — нет акции)
        ensure_column(c, "orders", "promo_code", "TEXT")
        ensure_column(c, "orders", "discount", "INTEGER NOT NULL DEFAULT 0")
        # reminded: 0 — нет, 1 — напомнили об оплате, 2 — продавец сказал «оплаты нет», не отменять само
        ensure_column(c, "orders", "reminded", "INTEGER NOT NULL DEFAULT 0")
        ensure_column(c, "promocodes", "owner_id", "INTEGER")  # личный промокод (приведи друга)
        # те, кто уже заказывал или писал до появления учёта, считаются пользователями
        c.execute(
            """INSERT OR IGNORE INTO users(user_id, username, full_name, first_seen, last_seen)
               SELECT user_id, MAX(username), MAX(full_name), MIN(created_at), MAX(created_at)
               FROM orders GROUP BY user_id"""
        )
        c.execute(
            """INSERT OR IGNORE INTO users(user_id, username, full_name, first_seen, last_seen)
               SELECT user_id, MAX(username), MAX(full_name), MIN(created_at), MAX(created_at)
               FROM suggestions GROUP BY user_id"""
        )

        if c.execute("SELECT COUNT(*) FROM products").fetchone()[0] == 0:
            c.executemany(
                "INSERT INTO products(name, price, stock, description, cost) VALUES(?,?,?,?,?)",
                SEED_PRODUCTS,
            )
        if first_cat:  # один раз при переходе на версию с категориями
            for r in c.execute("SELECT id, name FROM products").fetchall():
                if r["name"] in DEFAULT_CATEGORIES:
                    c.execute(
                        "UPDATE products SET category=? WHERE id=?", (DEFAULT_CATEGORIES[r["name"]], r["id"])
                    )
        for r in c.execute("SELECT id FROM products WHERE sku IS NULL OR sku=''").fetchall():
            c.execute("UPDATE products SET sku=? WHERE id=?", (make_sku(c, r["id"]), r["id"]))
        for r in c.execute("SELECT id, name, description FROM products").fetchall():
            if r["name"] in DEFAULT_DESCRIPTIONS and (
                r["description"] == "" or r["description"] in OLD_DESCRIPTIONS
            ):
                c.execute(
                    "UPDATE products SET description=? WHERE id=?",
                    (DEFAULT_DESCRIPTIONS[r["name"]], r["id"]),
                )
        for r in c.execute("SELECT id, name FROM products WHERE cost IS NULL").fetchall():
            if r["name"] in DEFAULT_COSTS:
                c.execute("UPDATE products SET cost=? WHERE id=?", (DEFAULT_COSTS[r["name"]], r["id"]))
        c.execute(
            "CREATE UNIQUE INDEX IF NOT EXISTS ux_products_sku ON products(sku COLLATE NOCASE)"
        )


def surcharge_active(now=None):
    """Действует ли сейчас ночная наценка (по умолчанию 02:00–06:00)."""
    if SURCHARGE_PERCENT <= 0 or SURCHARGE_FROM == SURCHARGE_TO:
        return False
    h = (now or datetime.now(ZoneInfo(TZ))).hour
    if SURCHARGE_FROM < SURCHARGE_TO:
        return SURCHARGE_FROM <= h < SURCHARGE_TO
    return h >= SURCHARGE_FROM or h < SURCHARGE_TO  # окно через полночь


def eff_price(base, now=None):
    """Цена для покупателя прямо сейчас: базовая или с наценкой (округление до рубля)."""
    if surcharge_active(now):
        return (base * (100 + SURCHARGE_PERCENT) + 50) // 100
    return base


def tariff_note():
    """Строка о тарифе для покупателя."""
    if surcharge_active():
        return (
            f"🌙 Ночной тариф: до {SURCHARGE_TO:02d}:00 цены +{SURCHARGE_PERCENT}% "
            "(уже учтено в ценах)."
        )
    return (
        f"🌙 С {SURCHARGE_FROM:02d}:00 до {SURCHARGE_TO:02d}:00 действует ночной тариф: "
        f"цены +{SURCHARGE_PERCENT}%."
    )


def cart_items(user_id):
    """price — цена с учётом акции (без ночной наценки), regular_price — обычная."""
    with db() as c:
        return c.execute(
            """SELECT p.id, p.name, COALESCE(p.sale_price, p.price) AS price,
                      p.price AS regular_price, p.stock, p.sku, k.qty
               FROM carts k JOIN products p ON p.id = k.product_id
               WHERE k.user_id = ? ORDER BY p.id""",
            (user_id,),
        ).fetchall()


def cart_add(user_id, pid):
    """Возвращает текст ошибки или None, если всё хорошо."""
    with db() as c:
        p = c.execute("SELECT stock, active FROM products WHERE id=?", (pid,)).fetchone()
        if not p or not p["active"]:
            return "Товар недоступен"
        row = c.execute(
            "SELECT qty FROM carts WHERE user_id=? AND product_id=?", (user_id, pid)
        ).fetchone()
        qty = row["qty"] if row else 0
        if qty + 1 > p["stock"]:
            return "Больше нет в наличии"
        c.execute(
            """INSERT INTO carts(user_id, product_id, qty) VALUES(?,?,1)
               ON CONFLICT(user_id, product_id) DO UPDATE SET qty = qty + 1""",
            (user_id, pid),
        )
    return None


def cart_dec(user_id, pid):
    with db() as c:
        c.execute(
            "UPDATE carts SET qty = qty - 1 WHERE user_id=? AND product_id=?",
            (user_id, pid),
        )
        c.execute("DELETE FROM carts WHERE user_id=? AND qty <= 0", (user_id,))


def cart_clear(user_id):
    with db() as c:
        c.execute("DELETE FROM carts WHERE user_id=?", (user_id,))
        c.execute("DELETE FROM cart_promos WHERE user_id=?", (user_id,))


# ── Настройки и режим работы ──
def get_setting(key, default=None):
    with db() as c:
        r = c.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
    return r["value"] if r else default


def set_setting(key, value):
    with db() as c:
        if value is None:
            c.execute("DELETE FROM settings WHERE key=?", (key,))
        else:
            c.execute(
                "INSERT INTO settings(key, value) VALUES(?,?) "
                "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                (key, str(value)),
            )


def parse_hhmm(s):
    """'22', '22:30' -> минуты от полуночи; иначе None."""
    m = re.fullmatch(r"(\d{1,2})(?::(\d{2}))?", (s or "").strip())
    if not m:
        return None
    h, mi = int(m.group(1)), int(m.group(2) or 0)
    if h > 23 or mi > 59:
        return None
    return h * 60 + mi


def fmt_min(x):
    return f"{x // 60:02d}:{x % 60:02d}"


def work_hours():
    """(с, до) в минутах или None, если магазин работает круглосуточно."""
    f, t = get_setting("work_from"), get_setting("work_to")
    if f is None:
        f = WORK_FROM
    if t is None:
        t = WORK_TO
    a, b = parse_hhmm(f), parse_hhmm(t)
    if a is None or b is None or a == b:
        return None
    return a, b


def shop_status(now=None):
    """(открыт_ли, строка_для_покупателя)."""
    now = now or datetime.now(ZoneInfo(TZ))
    if get_setting("manual_closed") == "1":
        return False, "🔴 " + (get_setting("closed_msg") or "Магазин временно закрыт.")
    wh = work_hours()
    if wh:
        cur, (a, b) = now.hour * 60 + now.minute, wh
        inside = (a <= cur < b) if a < b else (cur >= a or cur < b)
        if inside:
            return True, f"🟢 Открыто до {fmt_min(b)}"
        return False, f"🔴 Сейчас закрыто. Откроемся в {fmt_min(a)}"
    return True, "🟢 Работаем круглосуточно"


def schedule_text():
    wh = work_hours()
    return f"ежедневно {fmt_min(wh[0])}–{fmt_min(wh[1])}" if wh else "круглосуточно"


# ── Промокоды ──
PROMO_RE = re.compile(r"^[A-Za-z0-9_-]{2,20}$")


def promo_discount(c, code, user_id, subtotal):
    """(скидка, None) или (None, текст_ошибки). Код сравнивается в верхнем регистре."""
    code = (code or "").strip().upper()
    p = c.execute("SELECT * FROM promocodes WHERE code=?", (code,)).fetchone()
    if not p:
        return None, "Такого промокода нет."
    if p["owner_id"] is not None and p["owner_id"] != user_id:
        return None, "Этот промокод выдан другому человеку."
    if p["max_uses"] is not None and p["used"] >= p["max_uses"]:
        return None, "Промокод уже использован максимальное число раз."
    if c.execute(
        "SELECT 1 FROM promo_uses WHERE code=? AND user_id=?", (code, user_id)
    ).fetchone():
        return None, "Вы уже использовали этот промокод."
    d = (subtotal * p["percent"] + 50) // 100 if p["percent"] else p["amount"]
    d = min(d, max(subtotal - 1, 0))  # заказ не может стать бесплатным
    if d <= 0:
        return None, "Скидка не применима к этой сумме."
    return d, None


def cart_totals(user_id):
    """(товары, сумма, скидка, итого, промокод, ошибка_промокода)."""
    items = cart_items(user_id)
    subtotal = sum(eff_price(i["price"]) * i["qty"] for i in items)
    code = err = None
    discount = 0
    with db() as c:
        row = c.execute("SELECT code FROM cart_promos WHERE user_id=?", (user_id,)).fetchone()
        if row and items:
            d, err = promo_discount(c, row["code"], user_id, subtotal)
            if d is None:
                c.execute("DELETE FROM cart_promos WHERE user_id=?", (user_id,))
            else:
                code, discount = row["code"], d
    return items, subtotal, discount, subtotal - discount, code, err


# ── Поиск ──
def _stem(tok):
    """Грубо отрезаем окончание, чтобы «чипсов» находило «чипсы», «колу» — «Кола»."""
    if len(tok) >= 5:
        return tok[:-2]
    if len(tok) == 4:
        return tok[:-1]
    return tok


def search_products(query):
    q = " ".join((query or "").casefold().split())[:50]
    if not q:
        return []
    with db() as c:
        rows = c.execute("SELECT * FROM products WHERE active=1 ORDER BY id").fetchall()
    for p in rows:
        if (p["sku"] or "").casefold() == q:
            return [p]
    toks = [_stem(t) for t in q.split()]
    # сначала название / категория / артикул, и только если пусто — ещё и описание
    # (так «чипсы» найдёт Lay's и MultiChips, у которых в названии латиница)
    for fields in (("name", "category", "sku"), ("name", "category", "sku", "description")):
        out = [
            p for p in rows
            if all(t in " ".join(str(p[f] or "") for f in fields).casefold() for t in toks)
        ]
        if out:
            return out
    return []


def find_pid(token):
    """id товара по числовому id или артикулу."""
    with db() as c:
        if token.isdigit():
            r = c.execute("SELECT id FROM products WHERE id=?", (int(token),)).fetchone()
        else:
            r = c.execute("SELECT id FROM products WHERE lower(sku)=lower(?)", (token,)).fetchone()
    return r["id"] if r else None


def release_order(c, o):
    """Вернуть товары на склад и освободить промокод (при отмене заказа)."""
    for i in json.loads(o["items_json"]):
        c.execute("UPDATE products SET stock = stock + ? WHERE id=?", (i["qty"], i["id"]))
    if o["promo_code"]:
        c.execute("UPDATE promocodes SET used = MAX(used - 1, 0) WHERE code=?", (o["promo_code"],))
        c.execute("DELETE FROM promo_uses WHERE order_id=?", (o["id"],))


def process_reservations():
    """Бронь: отменяет неоплаченные заказы-переводы и находит те, кому пора напомнить.
    Возвращает (отменённые, для_напоминания)."""
    if RESERVE_MINUTES <= 0:
        return [], []
    now = datetime.now(ZoneInfo(TZ))
    fmt = "%Y-%m-%d %H:%M:%S"
    cut_exp = (now - timedelta(minutes=RESERVE_MINUTES)).strftime(fmt)
    cut_warn = (now - timedelta(minutes=RESERVE_MINUTES - 5)).strftime(fmt)
    base = "FROM orders WHERE payment='transfer' AND pay_status='unpaid' AND status='new'"
    expired, warn = [], []
    with db() as c:
        for o in c.execute(
            f"SELECT * {base} AND reminded<2 AND created_at <= ?", (cut_exp,)
        ).fetchall():
            release_order(c, o)
            c.execute("UPDATE orders SET status='cancelled' WHERE id=?", (o["id"],))
            expired.append(o)
        if RESERVE_MINUTES > 5:
            for o in c.execute(
                f"SELECT * {base} AND reminded=0 AND created_at <= ?", (cut_warn,)
            ).fetchall():
                c.execute("UPDATE orders SET reminded=1 WHERE id=?", (o["id"],))
                warn.append(o)
    return expired, warn


def place_order(user, payment):
    """Атомарно: проверка остатков, списание (= бронь товара), промокод, создание заказа.
    Возвращает ((order_id, items, total, discount, promo_code, low), None) или (None, ошибка).
    low — товары, у которых остаток стал <= LOW_STOCK."""
    with db() as c:
        rows = c.execute(
            """SELECT p.id, p.name, COALESCE(p.sale_price, p.price) AS price,
                      p.price AS regular_price, p.stock, p.sku, p.cost, k.qty
               FROM carts k JOIN products p ON p.id = k.product_id
               WHERE k.user_id = ? ORDER BY p.id""",
            (user.id,),
        ).fetchall()
        if not rows:
            return None, "Корзина пуста."
        active = c.execute(
            "SELECT COUNT(*) FROM orders WHERE user_id=? AND status IN ('new','ready')", (user.id,)
        ).fetchone()[0]
        if MAX_ACTIVE_ORDERS > 0 and active >= MAX_ACTIVE_ORDERS:
            return None, (
                f"Незавершённых заказов: {active} — это максимум. Дождитесь выдачи (или отмены), "
                "потом оформите новый. Статус: /myorders"
            )
        for r in rows:
            if r["qty"] > r["stock"]:
                return None, f"«{r['name']}»: осталось только {r['stock']} шт. Обновите корзину."
        now = datetime.now(ZoneInfo(TZ))
        # в заказ пишем цену, по которой клиент реально платит (акция + ночная наценка);
        # base_price — цена до наценки, она нужна продавцу, чтобы видеть наценку
        items = [
            {"id": r["id"], "name": r["name"], "sku": r["sku"],
             "price": eff_price(r["price"], now), "base_price": r["price"],
             "cost": r["cost"], "qty": r["qty"]}
            for r in rows
        ]
        subtotal = sum(i["price"] * i["qty"] for i in items)
        discount, code = 0, None
        prow = c.execute("SELECT code FROM cart_promos WHERE user_id=?", (user.id,)).fetchone()
        if prow:
            d, perr = promo_discount(c, prow["code"], user.id, subtotal)
            if d is None:
                c.execute("DELETE FROM cart_promos WHERE user_id=?", (user.id,))
                return None, f"Промокод больше не действует: {perr} Проверьте корзину и оформите заказ ещё раз."
            discount, code = d, prow["code"]
        total = subtotal - discount
        for i in items:
            c.execute("UPDATE products SET stock = stock - ? WHERE id=?", (i["qty"], i["id"]))
        cur = c.execute(
            """INSERT INTO orders(user_id, username, full_name, room, payment, total,
                                  items_json, created_at, promo_code, discount)
               VALUES(?,?,?,?,?,?,?,?,?,?)""",
            (
                user.id,
                user.username,
                user.full_name,
                "",  # комнату выдачи позже укажет продавец
                payment,
                total,
                json.dumps(items, ensure_ascii=False),
                now.strftime("%Y-%m-%d %H:%M:%S"),
                code,
                discount,
            ),
        )
        if code:
            c.execute("UPDATE promocodes SET used = used + 1 WHERE code=?", (code,))
            c.execute(
                "INSERT INTO promo_uses(code, user_id, order_id) VALUES(?,?,?)",
                (code, user.id, cur.lastrowid),
            )
        c.execute("DELETE FROM carts WHERE user_id=?", (user.id,))
        c.execute("DELETE FROM cart_promos WHERE user_id=?", (user.id,))
        low = []
        for i in items:
            s = c.execute("SELECT stock FROM products WHERE id=?", (i["id"],)).fetchone()["stock"]
            if s <= LOW_STOCK:
                low.append((i["name"], i["sku"], s))
        return (cur.lastrowid, items, total, discount, code, low), None


# ── Резервная копия и восстановление ──
def db_snapshot_bytes():
    """Цельный снимок базы (безопасно, даже если бот прямо сейчас пишет в неё)."""
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    try:
        s, d = sqlite3.connect(DB_PATH), sqlite3.connect(tmp)
        try:
            s.backup(d)
        finally:
            d.close()
            s.close()
        with open(tmp, "rb") as f:
            return f.read()
    finally:
        os.remove(tmp)


BACKUP_MAX_BYTES = 45 * 1024 * 1024  # лимит Telegram для ботов — 50 МБ
PHOTO_EXT_OK = (".jpg", ".jpeg", ".png", ".webp")


def make_backup():
    """(байты_zip, имя_файла, есть_ли_фото). В архиве: shop.db и папка photos/."""
    stamp = datetime.now(ZoneInfo(TZ)).strftime("%Y-%m-%d_%H%M")
    db_bytes = db_snapshot_bytes()
    photos = []
    if os.path.isdir(PHOTOS_DIR):
        photos = [
            f for f in sorted(os.listdir(PHOTOS_DIR))
            if f.lower().endswith(PHOTO_EXT_OK) and os.path.isfile(os.path.join(PHOTOS_DIR, f))
        ]
    for with_photos in (True, False):
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
            z.writestr("shop.db", db_bytes)
            if with_photos:
                for f in photos:
                    z.write(os.path.join(PHOTOS_DIR, f), "photos/" + f)
        if buf.tell() <= BACKUP_MAX_BYTES:
            return buf.getvalue(), f"shop_backup_{stamp}.zip", with_photos and bool(photos)
    raise ValueError("Резервная копия больше лимита Telegram (50 МБ).")


def restore_db_bytes(data):
    """Проверяет, что это база магазина, и переносит её в рабочую. Возвращает число товаров."""
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    try:
        with open(tmp, "wb") as f:
            f.write(data)
        s = sqlite3.connect(tmp)
        try:
            tables = {r[0] for r in s.execute("SELECT name FROM sqlite_master WHERE type='table'")}
            if not {"products", "orders"} <= tables:
                raise ValueError("Это не база магазина (нет таблиц товаров и заказов).")
            n = s.execute("SELECT COUNT(*) FROM products").fetchone()[0]
            d = sqlite3.connect(DB_PATH)
            try:
                s.backup(d)
            finally:
                d.close()
        except sqlite3.DatabaseError:
            raise ValueError("Файл повреждён или это не база SQLite.")
        finally:
            s.close()
    finally:
        os.remove(tmp)
    init_db()  # если копия старая — дотянуть таблицы и колонки до текущей версии
    return n


def restore_from_file(filename, data):
    """.db или .zip (shop.db + photos/). Возвращает (товаров, фото)."""
    name = (filename or "").lower()
    photos = 0
    if name.endswith(".zip"):
        try:
            z = zipfile.ZipFile(io.BytesIO(data))
        except zipfile.BadZipFile:
            raise ValueError("Не удалось открыть архив.")
        names = z.namelist()
        if "shop.db" not in names:
            raise ValueError("В архиве нет файла shop.db.")
        n = restore_db_bytes(z.read("shop.db"))
        os.makedirs(PHOTOS_DIR, exist_ok=True)
        for member in names:
            base = os.path.basename(member)
            if member.startswith("photos/") and base and base.lower().endswith(PHOTO_EXT_OK):
                with open(os.path.join(PHOTOS_DIR, base), "wb") as f:  # только имя файла: без ../
                    f.write(z.read(member))
                photos += 1
        return n, photos
    return restore_db_bytes(data), 0


def get_order(oid):
    with db() as c:
        return c.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
# ═══ DB END ═════════════════════════════════════════════════════════════


# ───────────────────────── Общее ─────────────────────────
async def safe_edit(message: Message, text: str, kb):
    if message.photo:
        # у сообщения с фото нельзя заменить подпись на обычный текст — шлём новое и удаляем старое
        try:
            await message.answer(text, reply_markup=kb)
            await message.delete()
        except TelegramBadRequest:
            pass
        return
    try:
        await message.edit_text(text, reply_markup=kb)
    except TelegramBadRequest:
        pass  # «message is not modified» и подобное — не страшно


def pay_line(o, for_seller=True):
    """Строка про оплату заказа."""
    if o["payment"] == "cash":
        base = "💵 Наличные при выдаче"
        return base + (" — ✅ получены" if o["pay_status"] == "paid" else "")
    seller = {
        "unpaid": "⏳ ждём оплату",
        "claimed": "🔔 клиент сообщил об оплате — проверьте поступление",
        "paid": "✅ оплата получена",
    }
    buyer = {
        "unpaid": "⏳ ждём оплату",
        "claimed": "🔔 проверяем оплату",
        "paid": "✅ оплачен",
    }
    return "💸 Перевод — " + (seller if for_seller else buyer)[o["pay_status"]]


# ═══ USERS BEGIN ═══ Пользователи, друзья, подписки на товары, поддержка ═══
def now_str():
    return datetime.now(ZoneInfo(TZ)).strftime("%Y-%m-%d %H:%M:%S")


def register_user(user, ref_id=None):
    """Запоминает человека, запустившего бота. True — он здесь впервые."""
    now = now_str()
    with db() as c:
        if c.execute("SELECT 1 FROM users WHERE user_id=?", (user.id,)).fetchone():
            c.execute(
                "UPDATE users SET username=?, full_name=?, last_seen=?, blocked=0 WHERE user_id=?",
                (user.username, user.full_name, now, user.id),
            )
            return False
        ref = None  # пригласить можно только того, кто ещё не пользовался ботом, и только существующим человеком
        if ref_id and ref_id != user.id and c.execute(
            "SELECT 1 FROM users WHERE user_id=?", (ref_id,)
        ).fetchone():
            ref = ref_id
        c.execute(
            "INSERT INTO users(user_id, username, full_name, first_seen, last_seen, referrer_id) "
            "VALUES(?,?,?,?,?,?)",
            (user.id, user.username, user.full_name, now, now, ref),
        )
        return True


def mark_blocked(user_id, flag=1):
    with db() as c:
        c.execute("UPDATE users SET blocked=? WHERE user_id=?", (flag, user_id))


def new_users_count(start=None, end=None):
    q, params = "SELECT COUNT(*) FROM users WHERE 1=1", []
    if start:
        q += " AND first_seen >= ?"
        params.append(start)
    if end:
        q += " AND first_seen < ?"
        params.append(end)
    with db() as c:
        return c.execute(q, params).fetchone()[0]


def users_summary_text():
    now = datetime.now(ZoneInfo(TZ))
    fmt = "%Y-%m-%d %H:%M:%S"
    today0 = now.replace(hour=0, minute=0, second=0, microsecond=0).strftime(fmt)
    d7, d30 = (now - timedelta(days=7)).strftime(fmt), (now - timedelta(days=30)).strftime(fmt)
    with db() as c:
        def q(sql, *a):
            return c.execute(sql, a).fetchone()[0]

        total = q("SELECT COUNT(*) FROM users")
        blocked = q("SELECT COUNT(*) FROM users WHERE blocked=1")
        unsub = q("SELECT COUNT(*) FROM users WHERE subscribed=0")
        can_send = q("SELECT COUNT(*) FROM users WHERE subscribed=1 AND blocked=0")
        buyers = q("SELECT COUNT(DISTINCT user_id) FROM orders WHERE status!='cancelled'")
        invited = q("SELECT COUNT(*) FROM users WHERE referrer_id IS NOT NULL")
        rewarded = q("SELECT COUNT(*) FROM users WHERE ref_rewarded=1")
        tops = c.execute(
            """SELECT x.referrer_id, x.n, x.r, u.full_name, u.username FROM (
                   SELECT referrer_id, COUNT(*) n, SUM(ref_rewarded) r FROM users
                   WHERE referrer_id IS NOT NULL GROUP BY referrer_id) x
               LEFT JOIN users u ON u.user_id = x.referrer_id ORDER BY x.n DESC, x.r DESC LIMIT 5"""
        ).fetchall()
        last = c.execute(
            "SELECT full_name, username, first_seen FROM users ORDER BY first_seen DESC, user_id DESC LIMIT 5"
        ).fetchall()
        stats = {
            "today": q("SELECT COUNT(*) FROM users WHERE first_seen >= ?", today0),
            "d7": q("SELECT COUNT(*) FROM users WHERE first_seen >= ?", d7),
            "d30": q("SELECT COUNT(*) FROM users WHERE first_seen >= ?", d30),
            "act7": q("SELECT COUNT(*) FROM users WHERE last_seen >= ?", d7),
            "tickets": q("SELECT COUNT(*) FROM tickets WHERE status='open'"),
            "waiters": q("SELECT COUNT(DISTINCT user_id) FROM stock_subs"),
        }
    out = ["👥 <b>Пользователи бота</b>", ""]
    out.append(f"Запустили бота: <b>{total}</b>")
    out.append(f"Новых: сегодня {stats['today']} · за 7 дней {stats['d7']} · за 30 дней {stats['d30']}")
    out.append(f"Заходили за последние 7 дней: {stats['act7']}")
    conv = f" ({round(buyers * 100 / total)}%)" if total else ""
    out.append(f"Сделали заказ: <b>{buyers}</b>{conv}")
    out.append(f"Получат рассылку: {can_send} · отписались: {unsub}")
    out.append(f"Заблокировали бота: {blocked}")
    if invited:
        out.append("")
        out.append(f"🎁 Пришли по приглашению: <b>{invited}</b> (награда выдана за {rewarded})")
        for t in tops:
            name = html.escape(t["full_name"] or str(t["referrer_id"]))
            if t["username"]:
                name += f" (@{html.escape(t['username'])})"
            out.append(f"  • {name} — {t['n']} (с заказом: {t['r'] or 0})")
    if stats["waiters"]:
        out.append("")
        out.append(f"🔔 Ждут товар (подписаны на поступление): {stats['waiters']} чел.")
    if stats["tickets"]:
        out.append(f"🆘 Открытых обращений: {stats['tickets']} (/tickets)")
    if last:
        out.append("")
        out.append("<b>Последние новые:</b>")
        for r in last:
            name = html.escape(r["full_name"] or "—")
            if r["username"]:
                name += f" (@{html.escape(r['username'])})"
            out.append(f"  • {name} — {r['first_seen'][5:16]}")
    out.append("\nСписок всех — кнопкой ниже, рассылка — /broadcast.")
    return "\n".join(out)


def users_csv_bytes():
    with db() as c:
        rows = c.execute(
            """SELECT u.*, COALESCE(a.n, 0) AS n, COALESCE(a.s, 0) AS s FROM users u
               LEFT JOIN (SELECT user_id, SUM(status != 'cancelled') AS n,
                                 SUM(CASE WHEN status='done' THEN total ELSE 0 END) AS s
                          FROM orders GROUP BY user_id) a ON a.user_id = u.user_id
               ORDER BY u.first_seen"""
        ).fetchall()
    buf = io.StringIO()
    w = csv.writer(buf, delimiter=";")
    w.writerow(["ID", "Username", "Имя", "Первый визит", "Последний визит", "Заказов",
                "Выдано на сумму, ₽", "Подписан на рассылку", "Заблокировал бота", "Пригласил (ID)"])
    for r in rows:
        w.writerow([
            r["user_id"], r["username"] or "", r["full_name"] or "", r["first_seen"], r["last_seen"],
            r["n"], r["s"], "да" if r["subscribed"] else "нет", "да" if r["blocked"] else "нет",
            r["referrer_id"] or "",
        ])
    return buf.getvalue().encode("utf-8-sig")


# ── Приведи друга ──
def make_personal_promo(user_id, amount):
    """Одноразовый промокод на amount ₽, который сможет применить только user_id."""
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    with db() as c:
        while True:
            code = "F" + "".join(random.choice(alphabet) for _ in range(6))
            if not c.execute("SELECT 1 FROM promocodes WHERE code=?", (code,)).fetchone():
                break
        c.execute(
            "INSERT INTO promocodes(code, percent, amount, max_uses, used, owner_id) VALUES(?,?,?,?,?,?)",
            (code, 0, amount, 1, 0, user_id),
        )
    return code


def referral_reward(o):
    """Вызывать, когда заказ o выдан. Если это первый зачётный заказ приглашённого —
    создаёт награду пригласившему и возвращает (referrer_id, промокод), иначе None."""
    if REF_REWARD_AMOUNT <= 0:
        return None
    with db() as c:
        u = c.execute(
            "SELECT referrer_id, ref_rewarded FROM users WHERE user_id=?", (o["user_id"],)
        ).fetchone()
        if not u or not u["referrer_id"] or u["ref_rewarded"] or o["total"] < REF_MIN_TOTAL:
            return None
        if REF_MAX_REWARDS > 0:
            n = c.execute(
                "SELECT COUNT(*) FROM users WHERE referrer_id=? AND ref_rewarded=1", (u["referrer_id"],)
            ).fetchone()[0]
            if n >= REF_MAX_REWARDS:
                return None
        c.execute("UPDATE users SET ref_rewarded=1 WHERE user_id=?", (o["user_id"],))
        rid = u["referrer_id"]
    return rid, make_personal_promo(rid, REF_REWARD_AMOUNT)


def ref_link(user_id):
    uname = bots.get("customer_username")
    return f"https://t.me/{uname}?start=ref_{user_id}" if uname else None


def friend_card(user_id):
    if REF_FRIEND_AMOUNT <= 0 and REF_REWARD_AMOUNT <= 0:
        return "🎁 Программа «Приведи друга» сейчас отключена.", None
    with db() as c:
        invited = c.execute("SELECT COUNT(*) FROM users WHERE referrer_id=?", (user_id,)).fetchone()[0]
        rewarded = c.execute(
            "SELECT COUNT(*) FROM users WHERE referrer_id=? AND ref_rewarded=1", (user_id,)
        ).fetchone()[0]
        codes = c.execute(
            "SELECT code, amount FROM promocodes WHERE owner_id=? AND (max_uses IS NULL OR used < max_uses) "
            "ORDER BY rowid", (user_id,),
        ).fetchall()
    link = ref_link(user_id)
    out = ["🎁 <b>Приведи друга</b>", ""]
    if REF_FRIEND_AMOUNT > 0:
        out.append(f"Друг, который придёт по вашей ссылке, получит <b>−{REF_FRIEND_AMOUNT} ₽</b> на первый заказ.")
    if REF_REWARD_AMOUNT > 0:
        out.append(
            f"А вы — <b>−{REF_REWARD_AMOUNT} ₽</b> на заказ, когда его первый заказ "
            f"(от {REF_MIN_TOTAL} ₽) будет выдан."
        )
    out.append("")
    out.append(f"🔗 Ваша ссылка:\n{link}" if link else "🔗 Ссылка появится через минуту — повторите /friend.")
    out.append(f"\nПриглашено: {invited} · из них получили награду: {rewarded}")
    if codes:
        out.append("\n🎟 <b>Ваши промокоды</b> (одноразовые, личные):")
        for r in codes:
            out.append(f"<code>{r['code']}</code> — −{r['amount']} ₽")
        out.append("Применить: «🏷 Ввести промокод» в корзине или /promo КОД")
    kb = None
    if link:
        share = (
            "https://t.me/share/url?url=" + quote(link, safe="")
            + "&text=" + quote("Ночной магазин в общаге — скидка на первый заказ по моей ссылке!")
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="📤 Отправить другу", url=share)]])
    return "\n".join(out), kb


# ── Подписка на поступление товара ──
def stock_sub_set(user_id, pid, want):
    """Включает/выключает подписку. Возвращает итоговое состояние (True — подписан)."""
    with db() as c:
        has = c.execute(
            "SELECT 1 FROM stock_subs WHERE user_id=? AND product_id=?", (user_id, pid)
        ).fetchone()
        if want and not has:
            c.execute(
                "INSERT INTO stock_subs(user_id, product_id, created_at) VALUES(?,?,?)",
                (user_id, pid, now_str()),
            )
        elif not want and has:
            c.execute("DELETE FROM stock_subs WHERE user_id=? AND product_id=?", (user_id, pid))
        return bool(want)


def stock_sub_has(user_id, pid):
    with db() as c:
        return c.execute(
            "SELECT 1 FROM stock_subs WHERE user_id=? AND product_id=?", (user_id, pid)
        ).fetchone() is not None


def user_sub_pids(user_id):
    with db() as c:
        return {r[0] for r in c.execute("SELECT product_id FROM stock_subs WHERE user_id=?", (user_id,))}


def sub_counts():
    """{id товара: сколько человек ждёт его появления}."""
    with db() as c:
        return {r[0]: r[1] for r in c.execute(
            "SELECT product_id, COUNT(*) FROM stock_subs GROUP BY product_id")}


def soldout_list_text():
    subs = sub_counts()
    with db() as c:
        rows = c.execute("SELECT id, name, sku FROM products WHERE active=1 AND stock<=0").fetchall()
    if not rows:
        return "\n\nСейчас всё в наличии 👍"
    rows = sorted(rows, key=lambda r: (-subs.get(r["id"], 0), r["id"]))
    return "\n\n<b>Нет в наличии:</b>\n" + "\n".join(
        f"• {html.escape(r['name'])} [{html.escape(r['sku'] or '-')}] — 🔔 ждут: {subs.get(r['id'], 0)}"
        for r in rows
    ) + "\nКак только вы пополните остаток (/setstock), подписчикам придёт уведомление."


# ── Поддержка ──
def open_ticket_of(user_id):
    with db() as c:
        return c.execute(
            "SELECT * FROM tickets WHERE user_id=? AND status='open' ORDER BY id DESC LIMIT 1", (user_id,)
        ).fetchone()


def get_ticket(tid):
    with db() as c:
        return c.execute("SELECT * FROM tickets WHERE id=?", (tid,)).fetchone()


def add_ticket_msg(user, text, has_photo, order_id=None):
    """Сообщение клиента: дописывается в его открытое обращение или создаёт новое.
    Возвращает (номер_обращения, это_новое_обращение)."""
    now = now_str()
    with db() as c:
        t = c.execute(
            "SELECT id FROM tickets WHERE user_id=? AND status='open' ORDER BY id DESC LIMIT 1", (user.id,)
        ).fetchone()
        if t:
            tid, is_new = t["id"], False
            c.execute(
                "UPDATE tickets SET updated_at=?, username=?, full_name=?, order_id=COALESCE(order_id, ?) "
                "WHERE id=?", (now, user.username, user.full_name, order_id, tid),
            )
        else:
            cur = c.execute(
                "INSERT INTO tickets(user_id, username, full_name, order_id, status, created_at, updated_at) "
                "VALUES(?,?,?,?, 'open', ?, ?)",
                (user.id, user.username, user.full_name, order_id, now, now),
            )
            tid, is_new = cur.lastrowid, True
        c.execute(
            "INSERT INTO ticket_msgs(ticket_id, from_seller, text, has_photo, created_at) VALUES(?,0,?,?,?)",
            (tid, text, int(has_photo), now),
        )
    return tid, is_new


def add_seller_msg(tid, text, has_photo):
    now = now_str()
    with db() as c:
        c.execute("UPDATE tickets SET updated_at=? WHERE id=?", (now, tid))
        c.execute(
            "INSERT INTO ticket_msgs(ticket_id, from_seller, text, has_photo, created_at) VALUES(?,1,?,?,?)",
            (tid, text, int(has_photo), now),
        )


def close_ticket(tid):
    with db() as c:
        c.execute("UPDATE tickets SET status='closed', updated_at=? WHERE id=?", (now_str(), tid))


def ticket_card_text(t, text, is_new, has_photo):
    who = f'<a href="tg://user?id={t["user_id"]}">{html.escape(t["full_name"] or "покупатель")}</a>'
    if t["username"]:
        who += f" (@{html.escape(t['username'])})"
    head = "🆘 <b>Новое обращение" if is_new else "💬 <b>Новое сообщение в обращении"
    out = [f"{head} #{t['id']}</b>", f"Клиент: {who} · ID <code>{t['user_id']}</code>"]
    if t["order_id"]:
        o = get_order(t["order_id"])
        if o:
            out.append(f"Заказ: #{o['id']} — {o['total']} ₽, {STATUS_LABELS[o['status']]}")
    body = html.escape(text) if text else ""
    if has_photo and not body:
        body = "📷 <i>(фото без подписи)</i>"
    return "\n".join(out + ["", body])


def ticket_kb(tid):
    kb = InlineKeyboardBuilder()
    kb.button(text="✉️ Ответить", callback_data=f"tk:r:{tid}")
    kb.button(text="✅ Закрыть", callback_data=f"tk:c:{tid}")
    kb.adjust(2)
    return kb.as_markup()


async def forward_ticket_to_seller(t, text, photo_id, is_new):
    card = ticket_card_text(t, text, is_new, bool(photo_id))
    try:
        if photo_id:  # file_id привязан к боту, поэтому перекачиваем файл
            buf = await bots["customer"].download(photo_id)
            await bots["seller"].send_photo(
                ADMIN_ID, BufferedInputFile(buf.read(), filename="photo.jpg"),
                caption=card[:1000], reply_markup=ticket_kb(t["id"]),
            )
        else:
            await bots["seller"].send_message(ADMIN_ID, card, reply_markup=ticket_kb(t["id"]))
    except Exception:
        logging.exception("Не удалось передать обращение продавцу")


# ── Рассылка ──
AUDIENCES = {
    "all": "👥 Все подписанные",
    "buyers": "🛒 Покупатели (были заказы)",
    "nobuy": "🙋 Ещё не покупали",
    "active": "🔥 Заходили за 30 дней",
}


def audience_ids(kind):
    sql = "SELECT u.user_id FROM users u WHERE u.subscribed=1 AND u.blocked=0"
    params = []
    has_order = "EXISTS (SELECT 1 FROM orders o WHERE o.user_id=u.user_id AND o.status!='cancelled')"
    if kind == "buyers":
        sql += f" AND {has_order}"
    elif kind == "nobuy":
        sql += f" AND NOT {has_order}"
    elif kind == "active":
        sql += " AND u.last_seen >= ?"
        params.append((datetime.now(ZoneInfo(TZ)) - timedelta(days=30)).strftime("%Y-%m-%d %H:%M:%S"))
    with db() as c:
        return [r[0] for r in c.execute(sql, params).fetchall()]
# ═══ USERS END ═══════════════════════════════════════════════════════════════


# ═══ SUG BEGIN ═══════════════ Предложения покупателей ═══════════════
SUG_ICONS = {"new": "🆕", "planned": "📌", "done": "✅", "rejected": "🚫"}
SUG_DAILY_LIMIT = 3


def add_suggestion(user, text):
    """Возвращает (id, None) или (None, текст_ошибки)."""
    text = " ".join(text.split())  # убираем переводы строк и лишние пробелы
    if len(text) < 3:
        return None, "Слишком коротко — опишите идею хотя бы парой слов."
    if len(text) > 300:
        return None, "Слишком длинно — уложитесь в 300 символов."
    now = datetime.now(ZoneInfo(TZ))
    with db() as c:
        n = c.execute(
            "SELECT COUNT(*) FROM suggestions WHERE user_id=? AND created_at >= ?",
            (user.id, now.strftime("%Y-%m-%d 00:00:00")),
        ).fetchone()[0]
        if n >= SUG_DAILY_LIMIT:
            return None, f"Лимит: не больше {SUG_DAILY_LIMIT} идей в день. Загляните завтра 🙂"
        cur = c.execute(
            "INSERT INTO suggestions(user_id, username, full_name, text, created_at) VALUES(?,?,?,?,?)",
            (user.id, user.username, user.full_name, text, now.strftime("%Y-%m-%d %H:%M:%S")),
        )
        c.execute(
            "INSERT INTO suggestion_votes(suggestion_id, user_id) VALUES(?,?)",
            (cur.lastrowid, user.id),
        )
    return cur.lastrowid, None


def toggle_vote(user_id, sid):
    """True — голос поставлен, False — снят, None — за это предложение уже нельзя голосовать."""
    with db() as c:
        s = c.execute("SELECT status FROM suggestions WHERE id=?", (sid,)).fetchone()
        if not s or s["status"] not in ("new", "planned"):
            return None
        had = c.execute(
            "SELECT 1 FROM suggestion_votes WHERE suggestion_id=? AND user_id=?", (sid, user_id)
        ).fetchone()
        if had:
            c.execute(
                "DELETE FROM suggestion_votes WHERE suggestion_id=? AND user_id=?", (sid, user_id)
            )
            return False
        c.execute("INSERT INTO suggestion_votes(suggestion_id, user_id) VALUES(?,?)", (sid, user_id))
        return True


_SUG_SELECT = """SELECT s.*,
    (SELECT COUNT(*) FROM suggestion_votes v WHERE v.suggestion_id = s.id) AS votes,
    (SELECT COUNT(*) FROM suggestion_votes v
        WHERE v.suggestion_id = s.id AND v.user_id = ?) AS mine
    FROM suggestions s """


def active_suggestions(user_id=None, limit=8):
    with db() as c:
        return c.execute(
            _SUG_SELECT + "WHERE s.status IN ('new','planned') ORDER BY votes DESC, s.id DESC LIMIT ?",
            (user_id or 0, limit),
        ).fetchall()


def get_suggestion(sid):
    with db() as c:
        return c.execute(_SUG_SELECT + "WHERE s.id = ?", (0, sid)).fetchone()
# ═══ SUG END ═══════════════════════════════════════════════════════════


# ═══ STATS BEGIN ═══════════════════ Статистика ═══════════════════
def shift_window(now):
    """Ночная смена, к которой относится момент now: [OPEN_HOUR сегодня/вчера, +длина смены).
    Днём возвращается последняя закончившаяся ночь."""
    day = now.date() if now.hour >= OPEN_HOUR else (now - timedelta(days=1)).date()
    start = datetime(day.year, day.month, day.day, OPEN_HOUR, 0, tzinfo=ZoneInfo(TZ))
    return start, start + timedelta(hours=24 - OPEN_HOUR + CLOSE_HOUR)


def stats_period(key, now=None):
    """Возвращает (start, end, подпись); start/end — строки в формате БД или None."""
    now = now or datetime.now(ZoneInfo(TZ))
    fmt = "%Y-%m-%d %H:%M:%S"
    if key == "night":
        start, end = shift_window(now)
        live = " (идёт сейчас)" if start <= now < end else ""
        return start.strftime(fmt), end.strftime(fmt), f"🌙 ночь {start:%d.%m} → {end:%d.%m}{live}"
    if key in ("7", "30"):
        return (now - timedelta(days=int(key))).strftime(fmt), None, f"последние {key} дней"
    return None, None, "всё время"


def rub(x):
    return f"{round(x):,}".replace(",", " ") + " ₽"


def compute_stats(start=None, end=None):
    with db() as c:
        costs = {r["id"]: r["cost"] for r in c.execute("SELECT id, cost FROM products")}
        q, params = "SELECT * FROM orders WHERE 1=1", []
        if start:
            q += " AND created_at >= ?"
            params.append(start)
        if end:
            q += " AND created_at < ?"
            params.append(end)
        orders = c.execute(q + " ORDER BY id", params).fetchall()
        low = c.execute(
            "SELECT name, sku, stock FROM products WHERE active=1 AND stock<=? ORDER BY stock, id",
            (LOW_STOCK,),
        ).fetchall()
        new_sug = c.execute("SELECT COUNT(*) FROM suggestions WHERE status='new'").fetchone()[0]

    cancelled = sum(1 for o in orders if o["status"] == "cancelled")
    live = [o for o in orders if o["status"] != "cancelled"]
    done = [o for o in live if o["status"] == "done"]
    active = [o for o in live if o["status"] in ACTIVE_STATUSES]

    products, profit, unknown_cost = {}, 0.0, False
    for o in live:
        for i in json.loads(o["items_json"]):
            row = products.setdefault(i["name"], {"qty": 0, "rev": 0, "profit": 0.0})
            row["qty"] += i["qty"]
            row["rev"] += i["price"] * i["qty"]
            cost = i.get("cost")
            if cost is None:
                cost = costs.get(i["id"])
            if cost is None:
                if o["status"] == "done":
                    unknown_cost = True
                continue
            gain = (i["price"] - cost) * i["qty"]
            row["profit"] += gain
            if o["status"] == "done":
                profit += gain

    for o in done:  # промокод уменьшает выручку, а значит и прибыль
        profit -= o["discount"] or 0

    buyers = Counter(o["user_id"] for o in live)
    unpaid = [o for o in active if o["payment"] == "transfer" and o["pay_status"] != "paid"]
    return {
        "orders": len(live),
        "done": len(done),
        "active": len(active),
        "cancelled": cancelled,
        "revenue": sum(o["total"] for o in done),
        "pending": sum(o["total"] for o in active),
        "avg": (sum(o["total"] for o in done) / len(done)) if done else 0,
        "profit": profit,
        "unknown_cost": unknown_cost,
        "unpaid_count": len(unpaid),
        "unpaid_sum": sum(o["total"] for o in unpaid),
        "transfer": sum(1 for o in live if o["payment"] == "transfer"),
        "cash": sum(1 for o in live if o["payment"] == "cash"),
        "buyers": len(buyers),
        "repeat": sum(1 for n in buyers.values() if n > 1),
        "top": sorted(products.items(), key=lambda kv: (-kv[1]["qty"], -kv[1]["rev"]))[:5],
        "hours": Counter(int(o["created_at"][11:13]) for o in live).most_common(3),
        "low": low,
        "new_sug": new_sug,
    }


def stats_text(key):
    start, end, label = stats_period(key)
    d = compute_stats(start, end)
    out = [f"📈 <b>Статистика — {label}</b>", ""]
    if not d["orders"] and not d["cancelled"]:
        out.append("За этот период заказов нет.")
    else:
        out.append(
            f"Заказы: <b>{d['orders']}</b> (выдано {d['done']}, в работе {d['active']}, "
            f"отменено {d['cancelled']})"
        )
        out.append(f"💰 Выручка (выдано): <b>{rub(d['revenue'])}</b>")
        profit_line = f"📊 Прибыль (выдано): <b>{rub(d['profit'])}</b>"
        if d["unknown_cost"]:
            profit_line += " (у части товаров не указана закупка — /setcost)"
        out.append(profit_line)
        if d["done"]:
            out.append(f"🧾 Средний чек: {rub(d['avg'])}")
        if d["active"]:
            out.append(f"⏳ В работе на сумму: {rub(d['pending'])}")
        if d["unpaid_count"]:
            out.append(
                f"💸 Ждёт оплаты переводом: {d['unpaid_count']} на {rub(d['unpaid_sum'])}"
            )
        out.append("")
        out.append(f"Оплата: перевод {d['transfer']} · наличные {d['cash']}")
        out.append(f"Клиенты: {d['buyers']} (вернулись снова: {d['repeat']})")
        if d["top"]:
            out.append("")
            out.append("🏆 <b>Топ товаров</b> (без отменённых)")
            for n, (name, v) in enumerate(d["top"], 1):
                out.append(
                    f"{n}. {html.escape(name)} — {v['qty']} шт., {rub(v['rev'])}, "
                    f"прибыль {rub(v['profit'])}"
                )
        if d["hours"]:
            out.append("")
            out.append(
                "🕐 <b>Горячие часы:</b> "
                + ", ".join(f"{h:02d}:00–{(h + 1) % 24:02d}:00 ({n})" for h, n in d["hours"])
            )
    out.append("")
    out.append(f"👥 Новых пользователей бота: <b>{new_users_count(start, end)}</b> (все — /users)")
    if d["low"]:
        out.append("")
        out.append("⚠️ <b>Заканчивается:</b>")
        for r in d["low"]:
            out.append(
                f"• {html.escape(r['name'])} [{html.escape(r['sku'] or '-')}] — "
                + (f"осталось {r['stock']}" if r["stock"] > 0 else "нет в наличии")
            )
    if d["new_sug"]:
        out.append("")
        out.append(f"💡 Новых предложений: {d['new_sug']} (/suggestions)")
    return "\n".join(out)


def stats_kb(active):
    kb = InlineKeyboardBuilder()
    for key, label in (("night", "🌙 Ночь"), ("7", "7 дней"), ("30", "30 дней"), ("all", "Всё время")):
        kb.button(text=("• " if key == active else "") + label, callback_data=f"st:{key}")
    kb.adjust(2)
    return kb.as_markup()
# ═══ STATS END ═════════════════════════════════════════════════════════


# ═════════════════════ БОТ ПОКУПАТЕЛЯ ═════════════════════
def cat_label(name):
    return name or "Другое"


def cat_key(name):
    """Короткий стабильный ключ категории для callback_data."""
    return format(zlib.crc32((name or "").encode("utf-8")), "x")


def _btn(text, data):
    return InlineKeyboardButton(text=text, callback_data=data)


def build_catalog(user_id, ctx=""):
    """ctx: '' — главная (меню категорий, если их больше одной), 'all' — все товары,
    'sale' — акции, иначе ключ категории (cat_key)."""
    with db() as c:
        allp = c.execute("SELECT * FROM products WHERE active=1 ORDER BY id").fetchall()
    soldout_all = [p for p in allp if p["stock"] <= 0]
    hide_mode = get_setting("soldout_mode", "hide") == "hide"
    if hide_mode:
        allp = [p for p in allp if p["stock"] > 0]  # вернутся сами, как только появится остаток
    else:
        allp = sorted(allp, key=lambda p: p["stock"] <= 0)  # закончившиеся — в конец списка
    cats = sorted({p["category"] or "" for p in allp}, key=lambda s: (s == "", s.casefold()))
    sale_n = sum(1 for p in allp if p["sale_price"])
    in_cart = sum(i["qty"] for i in cart_items(user_id))
    my_subs = user_sub_pids(user_id)
    _, status_line = shop_status()
    kb = InlineKeyboardBuilder()
    title, products = "", allp
    if not ctx and len(cats) > 1:
        products = None  # меню категорий
    elif ctx == "soldout":
        products, title = soldout_all, "🔔 Нет в наличии"
    elif ctx == "sale":
        products, title = [p for p in allp if p["sale_price"]], "🔥 Акции"
    elif ctx and ctx != "all":
        name = next((n for n in cats if cat_key(n) == ctx), None)
        if name is None:
            ctx = "all"
        else:
            products = [p for p in allp if (p["category"] or "") == name]
            title = cat_label(name)
    if ctx == "all":
        title = "Все товары"

    if products is None:
        if sale_n:
            kb.row(_btn(f"🔥 Акции ({sale_n})", "cg:sale"))
        for name in cats:
            n = sum(1 for p in allp if (p["category"] or "") == name)
            kb.row(_btn(f"{cat_label(name)} ({n})", f"cg:{cat_key(name)}"))
        kb.row(_btn("📋 Все товары", "cg:all"))
        hint = "Выберите раздел 👇\nМожно написать название или артикул товара (например, «чипсы» или <code>A002</code>)."
    else:
        for p in products:
            if p["stock"] > 0:
                base = p["sale_price"] or p["price"]
                fire = "🔥 " if p["sale_price"] else ""
                kb.row(
                    _btn(f"{fire}{p['name']} — {eff_price(base)} ₽", f"p:{p['id']}:{ctx}"),
                    _btn("➕", f"add:{p['id']}:{ctx}"),
                )
            else:
                kb.row(_btn(f"❌ {'🔔 ' if p['id'] in my_subs else ''}{p['name']} (нет в наличии)", f"p:{p['id']}:{ctx}"))
        if len(cats) > 1 or ctx == "soldout":
            kb.row(_btn("◀️ Категории" if len(cats) > 1 else "◀️ Каталог", "cat"))
        hint = (
            "Нажмите на название — откроется описание, на ➕ — товар сразу попадёт в корзину. "
            "Можно также написать название или артикул товара (например, <code>A002</code>)."
            if products
            else "Здесь пока пусто."
        )
    if ctx == "soldout":
        hint = "Нажмите на товар и выберите «🔔 Сообщить, когда появится» — напишем сразу, как он вернётся."
    if hide_mode and soldout_all and ctx != "soldout":
        kb.row(_btn(f"🔔 Нет в наличии ({len(soldout_all)}) — сообщить, когда появится", "cg:soldout"))
    kb.row(_btn("🔎 Поиск", "search"), _btn(f"🛒 Корзина ({in_cart})", "cart"))
    kb.row(_btn("💡 Предложить товар / идеи", "sg:list"))
    kb.row(_btn("🎁 Пригласить друга", "fr:open"), _btn("🆘 Поддержка", "sup:new"))
    text = f"🌙 <b>Ночной магазин</b>\n{status_line}\n{tariff_note()}\n\n"
    if title:
        text += f"<b>{html.escape(title)}</b>\n\n"
    text += hint + "\nМои заказы: /myorders"
    return text, kb.as_markup()


def build_card(user_id, pid, ctx=""):
    with db() as c:
        p = c.execute("SELECT * FROM products WHERE id=? AND active=1", (pid,)).fetchone()
    if not p:
        return None
    in_cart = sum(i["qty"] for i in cart_items(user_id))
    price = f"<b>{eff_price(p['sale_price'] or p['price'])} ₽</b>"
    if p["sale_price"]:
        price = f"🔥 <s>{eff_price(p['price'])} ₽</s> " + price + \
            f" (−{round((1 - p['sale_price'] / p['price']) * 100)}%)"
    text = (
        f"<b>{html.escape(p['name'])}</b>\n"
        f"Артикул: <code>{html.escape(p['sku'] or '-')}</code>\n"
        + (f"Категория: {html.escape(p['category'])}\n" if p["category"] else "")
        + f"Цена: {price}"
        + (f" (ночной тариф +{SURCHARGE_PERCENT}%)" if surcharge_active() else "")
        + "\n"
    )
    text += f"В наличии: {p['stock']} шт." if p["stock"] > 0 else "❌ Нет в наличии"
    subbed = p["stock"] <= 0 and stock_sub_has(user_id, pid)
    if subbed:
        text += "\n🔔 Вы подписаны — напишем, как только товар появится."
    if p["description"]:
        text += "\n\n" + html.escape(p["description"])
    kb = InlineKeyboardBuilder()
    if p["stock"] > 0:
        kb.button(text="➕ В корзину", callback_data=f"cadd:{pid}:{ctx}")
    elif subbed:
        kb.button(text="🔕 Не сообщать о поступлении", callback_data=f"unsub:{pid}:{ctx}")
    else:
        kb.button(text="🔔 Сообщить, когда появится", callback_data=f"sub:{pid}:{ctx}")
    kb.button(text=f"🛒 Корзина ({in_cart})", callback_data="cart")
    kb.button(text="◀️ Назад", callback_data=f"cg:{ctx}" if ctx else "cat")
    kb.adjust(1)
    return text, kb.as_markup()


def build_cart(user_id):
    items, subtotal, discount, total, code, perr = cart_totals(user_id)
    kb = InlineKeyboardBuilder()
    if not items:
        kb.button(text="◀️ В каталог", callback_data="cat")
        return "🛒 Корзина пуста.", kb.as_markup()
    lines = []
    for i in items:
        s = eff_price(i["price"]) * i["qty"]
        lines.append(f"• {html.escape(i['name'])} × {i['qty']} = {s} ₽")
        short = i["name"][:22]
        kb.button(text=f"➖ {short}", callback_data=f"dec:{i['id']}")
        kb.button(text=f"➕ {short}", callback_data=f"inc:{i['id']}")
    kb.button(text="🧹 Очистить", callback_data="clear")
    kb.button(text="◀️ В каталог", callback_data="cat")
    if code:
        kb.button(text=f"❌ Убрать промокод {code}", callback_data="promo:rm")
    else:
        kb.button(text="🏷 Ввести промокод", callback_data="promo:ask")
    kb.button(text="✅ Оформить заказ", callback_data="checkout")
    kb.adjust(*([2] * len(items)), 2, 1, 1)
    text = "🛒 <b>Ваша корзина</b>\n\n" + "\n".join(lines)
    if discount:
        text += f"\n\nСумма: {subtotal} ₽\n🏷 Промокод {html.escape(code)}: −{discount} ₽"
    text += f"\n\n<b>Итого: {total} ₽</b>"
    if perr:
        text += f"\n⚠️ Промокод снят: {html.escape(perr)}"
    if surcharge_active():
        text += f"\n{tariff_note()}"
    return text, kb.as_markup()


def payable(o):
    return (
        o["payment"] == "transfer"
        and o["pay_status"] == "unpaid"
        and o["status"] in ACTIVE_STATUSES
    )


@customer_router.message(CommandStart())
@customer_router.message(Command("menu"))
async def c_start(m: Message, state: FSMContext, new_user: bool = False):
    await state.clear()
    text, kb = build_catalog(m.from_user.id)
    await m.answer(text, reply_markup=kb)
    if new_user:
        await welcome_referred(m.from_user)


@customer_router.message(Command("myid"))
async def c_myid(m: Message):
    await m.answer(f"Ваш Telegram ID: <code>{m.from_user.id}</code>")


@customer_router.message(Command("myorders"))
async def c_myorders(m: Message):
    with db() as c:
        rows = c.execute(
            "SELECT * FROM orders WHERE user_id=? ORDER BY id DESC LIMIT 5", (m.from_user.id,)
        ).fetchall()
    if not rows:
        await m.answer("У вас пока нет заказов. Каталог — /menu")
        return
    lines, kb = [], InlineKeyboardBuilder()
    for o in rows:
        line = (
            f"{STATUS_ICONS[o['status']]} <b>Заказ #{o['id']}</b> — {o['total']} ₽, "
            f"{STATUS_LABELS[o['status']]}\n   {pay_line(o, for_seller=False)}"
        )
        if o["room"] and o["status"] in ACTIVE_STATUSES:
            line += f"\n   📍 Забирать: <b>{html.escape(o['room'])}</b>"
        lines.append(line)
        if payable(o):
            kb.button(text=f"💸 Я оплатил(а) #{o['id']}", callback_data=f"paid:{o['id']}")
        kb.button(text=f"🔁 Повторить #{o['id']}", callback_data=f"rep:{o['id']}")
        if o["status"] in ACTIVE_STATUSES:
            kb.button(text=f"🆘 Вопрос по заказу #{o['id']}", callback_data=f"sup:o:{o['id']}")
    kb.adjust(1)
    await m.answer("\n\n".join(lines), reply_markup=kb.as_markup())


@customer_router.callback_query(F.data.startswith("rep:"))
async def c_repeat(cb: CallbackQuery):
    o = get_order(int(cb.data.split(":")[1]))
    if not o or o["user_id"] != cb.from_user.id:
        await cb.answer("Заказ не найден", show_alert=True)
        return
    added, notes = 0, []
    for it in json.loads(o["items_json"]):
        got = 0
        for _ in range(it["qty"]):
            if cart_add(cb.from_user.id, it["id"]) is not None:
                break
            got += 1
        added += got
        if got < it["qty"]:
            notes.append(
                f"• {html.escape(it['name'])}: "
                + (f"добавил {got} из {it['qty']}" if got else "нет в наличии")
            )
    if not added:
        await cb.answer("Этих товаров сейчас нет в наличии", show_alert=True)
        return
    text, kb = build_cart(cb.from_user.id)
    note = f"🔁 Собрал корзину из заказа #{o['id']}.\n"
    if notes:
        note += "Не всё получилось:\n" + "\n".join(notes) + "\n"
    await cb.message.answer(note + "\n" + text, reply_markup=kb)
    await cb.answer("Добавлено в корзину ✅")


@customer_router.callback_query(F.data == "noop")
async def c_noop(cb: CallbackQuery):
    await cb.answer()


@customer_router.callback_query(F.data == "cat")
async def c_catalog(cb: CallbackQuery):
    text, kb = build_catalog(cb.from_user.id)
    await safe_edit(cb.message, text, kb)
    await cb.answer()


@customer_router.callback_query(F.data.startswith("cg:"))
async def c_category(cb: CallbackQuery):
    text, kb = build_catalog(cb.from_user.id, cb.data[3:])
    await safe_edit(cb.message, text, kb)
    await cb.answer()


@customer_router.callback_query(F.data == "search")
async def c_search_btn(cb: CallbackQuery):
    await cb.message.answer("🔎 Напишите название товара или артикул (например, «чипсы» или <code>A002</code>).")
    await cb.answer()


PHOTO_EXTS = (".jpg", ".jpeg", ".png", ".webp")


def photo_sources(p):
    """Варианты фото товара по порядку: кэш file_id, ссылка/файл из БД, файл photos/<артикул|id>.*"""
    out = []
    if p["photo_fid"]:
        out.append(("fid", p["photo_fid"]))
    ph = (p["photo"] or "").strip()
    if ph.lower().startswith(("http://", "https://")):
        out.append(("url", ph))
    elif ph:
        out.append(("file", os.path.join(PHOTOS_DIR, os.path.basename(ph))))
    for stem in (p["sku"], str(p["id"])):
        for ext in PHOTO_EXTS:
            if stem:
                out.append(("file", os.path.join(PHOTOS_DIR, stem + ext)))
    return out


async def send_card_photo(message: Message, p, text, kb):
    """Пробует отправить карточку с фото. True — получилось, False — фото нет или не грузится."""
    for kind, src in photo_sources(p):
        if kind == "file" and not os.path.isfile(src):
            continue
        try:
            sent = await message.answer_photo(
                FSInputFile(src) if kind == "file" else src, caption=text, reply_markup=kb
            )
        except Exception:  # битая ссылка, устаревший file_id, слишком большой файл…
            logging.warning("Фото товара %s не отправилось (%s: %s)", p["id"], kind, src)
            if kind == "fid":
                with db() as c:
                    c.execute("UPDATE products SET photo_fid=NULL WHERE id=?", (p["id"],))
            continue
        if kind != "fid":
            with db() as c:
                c.execute(
                    "UPDATE products SET photo_fid=? WHERE id=?", (sent.photo[-1].file_id, p["id"])
                )
        return True
    return False


async def show_card(message: Message, user_id, pid, replace=True, ctx=""):
    """Показывает карточку товара: с фото, если оно есть, иначе текстом.
    replace=True — заменяет сообщение, из которого открыли карточку."""
    card = build_card(user_id, pid, ctx)
    if not card:
        return False
    text, kb = card
    with db() as c:
        p = c.execute("SELECT * FROM products WHERE id=?", (pid,)).fetchone()
    if await send_card_photo(message, p, text, kb):
        if replace:
            try:
                await message.delete()
            except TelegramBadRequest:
                pass
    elif replace:
        await safe_edit(message, text, kb)
    else:
        await message.answer(text, reply_markup=kb)
    return True


def _pid_ctx(data):
    """'p:5:abc' -> (5, 'abc'); 'p:5' (старые кнопки) -> (5, '')."""
    parts = data.split(":")
    return int(parts[1]), (parts[2] if len(parts) > 2 else "")


@customer_router.callback_query(F.data.startswith("p:"))
async def c_card(cb: CallbackQuery):
    pid, ctx = _pid_ctx(cb.data)
    if not await show_card(cb.message, cb.from_user.id, pid, ctx=ctx):
        await cb.answer("Товар недоступен", show_alert=True)
        return
    await cb.answer()


@customer_router.callback_query(F.data.startswith("add:"))
async def c_add(cb: CallbackQuery):
    pid, ctx = _pid_ctx(cb.data)
    err = cart_add(cb.from_user.id, pid)
    if err:
        await cb.answer(err, show_alert=True)
        return
    _, kb = build_catalog(cb.from_user.id, ctx)
    try:
        await cb.message.edit_reply_markup(reply_markup=kb)
    except TelegramBadRequest:
        pass
    await cb.answer("Добавлено в корзину ✅")


@customer_router.callback_query(F.data.startswith("cadd:"))
async def c_card_add(cb: CallbackQuery):
    pid, ctx = _pid_ctx(cb.data)
    err = cart_add(cb.from_user.id, pid)
    if err:
        await cb.answer(err, show_alert=True)
        return
    card = build_card(cb.from_user.id, pid, ctx)
    if card:
        try:
            if cb.message.photo:
                await cb.message.edit_caption(caption=card[0], reply_markup=card[1])
            else:
                await cb.message.edit_text(card[0], reply_markup=card[1])
        except TelegramBadRequest:
            pass
    await cb.answer("Добавлено в корзину ✅")


@customer_router.callback_query(F.data == "cart")
async def c_cart(cb: CallbackQuery):
    text, kb = build_cart(cb.from_user.id)
    await safe_edit(cb.message, text, kb)
    await cb.answer()


@customer_router.callback_query(F.data.startswith("inc:"))
async def c_inc(cb: CallbackQuery):
    err = cart_add(cb.from_user.id, int(cb.data.split(":")[1]))
    if err:
        await cb.answer(err, show_alert=True)
        return
    text, kb = build_cart(cb.from_user.id)
    await safe_edit(cb.message, text, kb)
    await cb.answer()


@customer_router.callback_query(F.data.startswith("dec:"))
async def c_dec(cb: CallbackQuery):
    cart_dec(cb.from_user.id, int(cb.data.split(":")[1]))
    text, kb = build_cart(cb.from_user.id)
    await safe_edit(cb.message, text, kb)
    await cb.answer()


@customer_router.callback_query(F.data == "clear")
async def c_clear(cb: CallbackQuery):
    cart_clear(cb.from_user.id)
    text, kb = build_cart(cb.from_user.id)
    await safe_edit(cb.message, text, kb)
    await cb.answer("Корзина очищена")


@customer_router.callback_query(F.data == "checkout")
async def c_checkout(cb: CallbackQuery):
    is_open, status = shop_status()
    if not is_open:
        await cb.answer(status[2:].strip(), show_alert=True)
        return
    items, subtotal, discount, total, code, perr = cart_totals(cb.from_user.id)
    if not items:
        await cb.answer("Корзина пуста", show_alert=True)
        return
    kb = InlineKeyboardBuilder()
    kb.button(text="💸 Перевод", callback_data="pay:transfer")
    kb.button(text="💵 Наличные", callback_data="pay:cash")
    kb.adjust(2)
    await cb.message.answer(
        f"Сумма заказа: <b>{total} ₽</b>"
        + (f" (промокод {html.escape(code)}: −{discount} ₽)" if discount else "")
        + "\nКак будете платить?",
        reply_markup=kb.as_markup(),
    )
    await cb.answer()


async def notify_seller(text, kb=None):
    try:
        await bots["seller"].send_message(ADMIN_ID, text, reply_markup=kb)
    except Exception:
        logging.exception(
            "Не удалось написать продавцу. Продавец должен нажать /start в боте продавца."
        )


@customer_router.callback_query(F.data.startswith("pay:"))
async def c_pay(cb: CallbackQuery):
    payment = cb.data.split(":")[1]
    if payment not in PAY_LABELS:
        await cb.answer()
        return
    is_open, status = shop_status()
    if not is_open:
        await cb.message.edit_text(f"{status}\n\nКорзина сохранена, оформите заказ, когда откроемся: /menu")
        await cb.answer()
        return
    result, err = place_order(cb.from_user, payment)
    if err:
        await cb.message.edit_text(f"⚠️ {err}\n\n/menu")
        await cb.answer()
        return
    oid, items, total, discount, code, low = result

    msg = f"✅ <b>Заказ #{oid} принят!</b>\nСумма: <b>{total} ₽</b>."
    if discount:
        msg += f"\n🏷 Промокод {html.escape(code)}: −{discount} ₽"
    kb = None
    if payment == "transfer":
        msg += (
            f"\n\n💸 Оплата переводом:\n{html.escape(PAYMENT_INFO)}\n\n"
            "После перевода нажмите кнопку ниже — продавец проверит и подтвердит оплату."
        )
        if RESERVE_MINUTES > 0:
            msg += (
                f"\n\n⏱ Товар забронирован на {RESERVE_MINUTES} мин. Если оплата не придёт, "
                "заказ отменится автоматически."
            )
        b = InlineKeyboardBuilder()
        b.button(text="💸 Я оплатил(а)", callback_data=f"paid:{oid}")
        kb = b.as_markup()
    else:
        msg += "\n\n💵 Оплата наличными при получении."
    msg += "\n\nКак только соберём заказ, напишем, в какую комнату подойти. Статус: /myorders"
    await cb.message.edit_text(msg, reply_markup=kb)
    await cb.answer()

    o = get_order(oid)
    await notify_seller(admin_order_text(o), admin_order_kb(o))
    for name, sku, stock in low:
        await notify_seller(
            f"⚠️ <b>{'Закончился' if stock <= 0 else 'Заканчивается'}:</b> {html.escape(name)} "
            f"[{html.escape(sku or '-')}] — "
            + ("остаток 0, товар недоступен для заказа" if stock <= 0 else f"осталось {stock} шт.")
            + "\nПополнить: /setstock id кол-во"
        )


@customer_router.callback_query(F.data.startswith("paid:"))
async def c_paid(cb: CallbackQuery):
    oid = int(cb.data.split(":")[1])
    err = None
    with db() as c:
        o = c.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
        if not o or o["user_id"] != cb.from_user.id:
            err = "Заказ не найден"
        elif o["status"] not in ACTIVE_STATUSES:
            err = "Заказ уже закрыт"
        elif o["payment"] != "transfer":
            err = "Этот заказ оплачивается наличными"
        elif o["pay_status"] == "paid":
            err = "Оплата уже подтверждена ✅"
        elif o["pay_status"] == "claimed":
            err = "Уже отправлено продавцу — ждите подтверждения"
        else:
            c.execute("UPDATE orders SET pay_status='claimed' WHERE id=?", (oid,))
    if err:
        await cb.answer(err, show_alert=True)
        return
    await cb.answer("Отправил продавцу ✅")
    await cb.message.answer(
        f"Спасибо! Продавец проверит перевод по заказу #{oid} и подтвердит оплату."
    )
    o = get_order(oid)
    await notify_seller("🔔 <b>Клиент сообщил об оплате</b>\n\n" + admin_order_text(o), admin_order_kb(o))


# ── Предложения покупателей ──
def build_suggestions(user_id):
    rows = active_suggestions(user_id, 8)
    kb = InlineKeyboardBuilder()
    if not rows:
        text = "💡 <b>Предложения</b>\nПока ничего нет — предложите первым!"
    else:
        lines = []
        for n, r in enumerate(rows, 1):
            plan = " 📌 в планах" if r["status"] == "planned" else ""
            lines.append(f"{n}. {html.escape(r['text'])} — 👍 {r['votes']}{plan}")
            kb.row(
                InlineKeyboardButton(
                    text=f"{'✅' if r['mine'] else '👍'} {n}. {r['text'][:24]}",
                    callback_data=f"sgv:{r['id']}",
                )
            )
        text = (
            "💡 <b>Что добавить в магазин?</b>\n"
            "Голосуйте за идеи других (повторное нажатие снимает голос) или предложите своё.\n\n"
            + "\n".join(lines)
        )
    kb.row(InlineKeyboardButton(text="✍️ Предложить своё", callback_data="sg:new"))
    kb.row(InlineKeyboardButton(text="◀️ Каталог", callback_data="cat"))
    return text, kb.as_markup()


SUGGEST_PROMPT = (
    "✍️ Напишите одним сообщением, что добавить в магазин: товар, марка, вкус или любая идея "
    "(до 300 символов).\nОтмена — /cancel"
)


@customer_router.callback_query(F.data == "sg:list")
async def c_sug_list(cb: CallbackQuery):
    await safe_edit(cb.message, *build_suggestions(cb.from_user.id))
    await cb.answer()


@customer_router.callback_query(F.data.startswith("sgv:"))
async def c_sug_vote(cb: CallbackQuery):
    voted = toggle_vote(cb.from_user.id, int(cb.data.split(":")[1]))
    if voted is None:
        await cb.answer("За эту идею уже нельзя голосовать", show_alert=True)
    else:
        await cb.answer("Голос учтён 👍" if voted else "Голос снят")
    await safe_edit(cb.message, *build_suggestions(cb.from_user.id))


@customer_router.callback_query(F.data == "sg:new")
async def c_sug_new(cb: CallbackQuery, state: FSMContext):
    await state.set_state(Suggest.text)
    await cb.message.answer(SUGGEST_PROMPT)
    await cb.answer()


@customer_router.message(Command("suggest"))
async def c_suggest_cmd(m: Message, state: FSMContext):
    await state.set_state(Suggest.text)
    await m.answer(SUGGEST_PROMPT)


@customer_router.message(Command("cancel"))
async def c_cancel(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Отменено. Каталог — /menu")


@customer_router.message(Suggest.text, F.text)
async def c_suggest_text(m: Message, state: FSMContext):
    if m.text.startswith("/"):
        await m.answer("Напишите идею обычным сообщением или нажмите /cancel.")
        return
    sid, err = add_suggestion(m.from_user, m.text)
    if err:
        if err.startswith("Лимит"):
            await state.clear()
        await m.answer(f"⚠️ {err}")
        return
    await state.clear()
    await m.answer(
        "Спасибо за идею! 🙌 Она появилась в списке — другие смогут за неё проголосовать. "
        "Если добавим, обязательно напишем.\nСписок идей: /ideas"
    )
    s = get_suggestion(sid)
    await notify_seller("💡 <b>Новая идея</b>\n\n" + sug_card_text(s), sug_kb(s))


@customer_router.message(Command("ideas"))
async def c_ideas(m: Message):
    text, kb = build_suggestions(m.from_user.id)
    await m.answer(text, reply_markup=kb)


# ── Промокоды ──
PROMO_PROMPT = "🏷 Введите промокод одним сообщением.\nОтмена — /cancel"


async def promo_apply(m: Message, code):
    """True — промокод применён к корзине."""
    code = code.strip().upper()
    items, subtotal, *_ = cart_totals(m.from_user.id)
    if not items:
        await m.answer("Сначала добавьте товары в корзину: /menu")
        return True
    with db() as c:
        d, err = promo_discount(c, code, m.from_user.id, subtotal)
        if d is not None:
            c.execute(
                "INSERT INTO cart_promos(user_id, code) VALUES(?,?) "
                "ON CONFLICT(user_id) DO UPDATE SET code=excluded.code",
                (m.from_user.id, code),
            )
    if d is None:
        await m.answer(f"⚠️ {err}")
        return False
    text, kb = build_cart(m.from_user.id)
    await m.answer(f"✅ Промокод применён: −{d} ₽\n\n{text}", reply_markup=kb)
    return True


@customer_router.callback_query(F.data == "promo:ask")
async def c_promo_ask(cb: CallbackQuery, state: FSMContext):
    await state.set_state(PromoInput.code)
    await cb.message.answer(PROMO_PROMPT)
    await cb.answer()


@customer_router.callback_query(F.data == "promo:rm")
async def c_promo_rm(cb: CallbackQuery):
    with db() as c:
        c.execute("DELETE FROM cart_promos WHERE user_id=?", (cb.from_user.id,))
    await safe_edit(cb.message, *build_cart(cb.from_user.id))
    await cb.answer("Промокод убран")


@customer_router.message(Command("promo"))
async def c_promo_cmd(m: Message, state: FSMContext):
    parts = m.text.split(maxsplit=1)
    if len(parts) == 2:
        if await promo_apply(m, parts[1]):
            await state.clear()
        return
    await state.set_state(PromoInput.code)
    await m.answer(PROMO_PROMPT)


@customer_router.message(PromoInput.code, F.text)
async def c_promo_text(m: Message, state: FSMContext):
    if m.text.startswith("/"):
        await m.answer("Напишите промокод обычным сообщением или нажмите /cancel.")
        return
    if await promo_apply(m, m.text):
        await state.clear()


# ── Режим работы ──
@customer_router.message(Command("hours"))
async def c_hours(m: Message):
    _, status = shop_status()
    await m.answer(f"{status}\n🕐 Режим работы: {schedule_text()}\n{tariff_note()}")


# ── Приведи друга ──
async def welcome_referred(user):
    """Новый человек пришёл по ссылке друга: даём ему промокод и сообщаем пригласившему."""
    with db() as c:
        u = c.execute("SELECT referrer_id FROM users WHERE user_id=?", (user.id,)).fetchone()
    if not u or not u["referrer_id"]:
        return
    if REF_FRIEND_AMOUNT > 0:
        code = make_personal_promo(user.id, REF_FRIEND_AMOUNT)
        await tell_customer(
            user.id,
            f"🎁 Вас пригласил друг! Промокод на первый заказ: <code>{code}</code> — "
            f"<b>−{REF_FRIEND_AMOUNT} ₽</b>.\nПримените его в корзине («🏷 Ввести промокод») или командой "
            f"<code>/promo {code}</code>",
        )
    if REF_REWARD_AMOUNT > 0:
        await tell_customer(
            u["referrer_id"],
            f"👋 По вашей ссылке в магазин пришёл(а) {html.escape(user.full_name)}. Как только первый заказ "
            f"друга (от {REF_MIN_TOTAL} ₽) будет выдан, вы получите промокод на −{REF_REWARD_AMOUNT} ₽.",
        )


@customer_router.message(Command("friend"))
async def c_friend(m: Message):
    text, kb = friend_card(m.from_user.id)
    await m.answer(text, reply_markup=kb, disable_web_page_preview=True)


@customer_router.callback_query(F.data == "fr:open")
async def c_friend_btn(cb: CallbackQuery):
    text, kb = friend_card(cb.from_user.id)
    await cb.message.answer(text, reply_markup=kb, disable_web_page_preview=True)
    await cb.answer()


# ── Сообщить, когда товар появится ──
@customer_router.callback_query(F.data.startswith("sub:") | F.data.startswith("unsub:"))
async def c_stock_sub(cb: CallbackQuery):
    pid, ctx = _pid_ctx(cb.data)
    want = cb.data.startswith("sub:")
    with db() as c:
        p = c.execute("SELECT stock, active FROM products WHERE id=?", (pid,)).fetchone()
    if not p or not p["active"]:
        await cb.answer("Товар недоступен", show_alert=True)
        return
    if want and p["stock"] > 0:
        await cb.answer("Товар уже в наличии — можно заказывать!", show_alert=True)
    elif want and len(user_sub_pids(cb.from_user.id)) >= 15:
        await cb.answer("Можно ждать не больше 15 товаров сразу. Отпишитесь от ненужных.", show_alert=True)
        return
    else:
        stock_sub_set(cb.from_user.id, pid, want)
        await cb.answer(
            "🔔 Готово! Напишу, как только товар появится" if want else "Хорошо, напоминать не буду"
        )
    card = build_card(cb.from_user.id, pid, ctx)
    if card:
        try:
            if cb.message.photo:
                await cb.message.edit_caption(caption=card[0], reply_markup=card[1])
            else:
                await cb.message.edit_text(card[0], reply_markup=card[1])
        except TelegramBadRequest:
            pass


# ── Рассылка: подписка/отписка ──
def news_card(user_id):
    with db() as c:
        u = c.execute("SELECT subscribed FROM users WHERE user_id=?", (user_id,)).fetchone()
    on = (not u) or bool(u["subscribed"])
    kb = InlineKeyboardBuilder()
    kb.button(text="🔕 Отписаться" if on else "🔔 Подписаться", callback_data="news:off" if on else "news:on")
    text = (
        "🔔 Рассылка: <b>включена</b>. Иногда пишем об акциях и новинках.\n"
        "Сообщения о ваших заказах, ответы поддержки и уведомления о поступлении товара придут в любом случае."
        if on else
        "🔕 Рассылка: <b>выключена</b>. Об акциях и новинках писать не будем.\n"
        "Сообщения о ваших заказах и уведомления о поступлении товара продолжат приходить."
    )
    return text, kb.as_markup()


@customer_router.message(Command("news"))
async def c_news(m: Message):
    text, kb = news_card(m.from_user.id)
    await m.answer(text, reply_markup=kb)


@customer_router.callback_query(F.data.in_({"news:on", "news:off"}))
async def c_news_toggle(cb: CallbackQuery):
    with db() as c:
        c.execute(
            "UPDATE users SET subscribed=? WHERE user_id=?", (1 if cb.data == "news:on" else 0, cb.from_user.id)
        )
    text, kb = news_card(cb.from_user.id)
    try:
        await cb.message.edit_reply_markup(reply_markup=None)
    except TelegramBadRequest:
        pass
    await cb.message.answer(text, reply_markup=kb)
    await cb.answer("Готово")


@customer_router.my_chat_member()
async def c_member_update(ev: ChatMemberUpdated):
    """Человек заблокировал или разблокировал бота."""
    if ev.chat.type != "private":
        return
    mark_blocked(ev.from_user.id, 1 if ev.new_chat_member.status in ("kicked", "left") else 0)


# ── Поддержка ──
SUPPORT_PROMPT = (
    "🆘 <b>Поддержка</b>\n"
    "Опишите вопрос или проблему одним сообщением (можно с фото, до 600 символов). "
    "Ответ придёт сюда, в этот чат.\nОтмена — /cancel"
)
_support_last = {}


async def support_start(message: Message, state: FSMContext, user, order_id=None):
    t = open_ticket_of(user.id)
    await state.set_state(Support.text)
    await state.update_data(order_id=order_id)
    extra = ""
    if order_id:
        extra += f"\n\n📦 Вопрос по заказу #{order_id}"
    if t:
        extra += f"\n\nУ вас уже есть открытое обращение #{t['id']} — это сообщение его дополнит."
    await message.answer(SUPPORT_PROMPT + extra)


@customer_router.message(Command("support"))
async def c_support_cmd(m: Message, state: FSMContext):
    await support_start(m, state, m.from_user)


@customer_router.callback_query(F.data == "sup:new")
async def c_support_btn(cb: CallbackQuery, state: FSMContext):
    await support_start(cb.message, state, cb.from_user)
    await cb.answer()


@customer_router.callback_query(F.data.startswith("sup:o:"))
async def c_support_order(cb: CallbackQuery, state: FSMContext):
    o = get_order(int(cb.data.split(":")[2]))
    if not o or o["user_id"] != cb.from_user.id:
        await cb.answer("Заказ не найден", show_alert=True)
        return
    await support_start(cb.message, state, cb.from_user, order_id=o["id"])
    await cb.answer()


@customer_router.callback_query(F.data.startswith("sup:more:"))
async def c_support_more(cb: CallbackQuery, state: FSMContext):
    t = get_ticket(int(cb.data.split(":")[2]))
    if not t or t["user_id"] != cb.from_user.id:
        await cb.answer("Обращение не найдено", show_alert=True)
        return
    await support_start(cb.message, state, cb.from_user)
    await cb.answer()


@customer_router.callback_query(F.data.startswith("sup:done:"))
async def c_support_done(cb: CallbackQuery):
    t = get_ticket(int(cb.data.split(":")[2]))
    if not t or t["user_id"] != cb.from_user.id:
        await cb.answer("Обращение не найдено", show_alert=True)
        return
    if t["status"] == "open":
        close_ticket(t["id"])
        await notify_seller(f"✅ Клиент закрыл обращение #{t['id']}: вопрос решён.")
    try:
        await cb.message.edit_reply_markup(reply_markup=None)
    except TelegramBadRequest:
        pass
    await cb.answer("Рады, что всё решилось! 🙌")


@customer_router.message(Support.text, F.text | F.photo)
async def c_support_msg(m: Message, state: FSMContext):
    if m.text and m.text.startswith("/"):
        await m.answer("Напишите вопрос обычным сообщением или нажмите /cancel.")
        return
    now = time.monotonic()
    wait = SUPPORT_MIN_GAP - (now - _support_last.get(m.from_user.id, -1e9))
    if wait > 0:
        await m.answer(f"⏳ Подождите {int(wait) + 1} сек. и отправьте ещё раз.")
        return
    text = (m.text or m.caption or "").strip()
    photo_id = m.photo[-1].file_id if m.photo else None
    if not text and not photo_id:
        return
    if len(text) > 600:
        await m.answer(f"Слишком длинно ({len(text)} из 600 символов). Сократите, пожалуйста.")
        return
    data = await state.get_data()
    await state.clear()
    _support_last[m.from_user.id] = now
    tid, is_new = add_ticket_msg(m.from_user, text, bool(photo_id), data.get("order_id"))
    await forward_ticket_to_seller(get_ticket(tid), text, photo_id, is_new)
    await m.answer(f"✅ Передал в поддержку (обращение #{tid}). Ответим здесь, в этом чате.")


# ── Поиск: по артикулу или названию — последним, чтобы не мешать командам ──
async def do_search(m: Message, query):
    found = search_products(query)
    if not found:
        await m.answer(
            f"Ничего не нашёл по «{html.escape(query.strip()[:50])}». "
            "Попробуйте другое слово или откройте каталог — /menu"
        )
        return
    if len(found) == 1:
        await show_card(m, m.from_user.id, found[0]["id"], replace=False)
        return
    kb = InlineKeyboardBuilder()
    for p in found[:10]:
        base = p["sale_price"] or p["price"]
        label = f"{p['name']} — {eff_price(base)} ₽" if p["stock"] > 0 else f"❌ {p['name']}"
        kb.button(text=("🔥 " if p["sale_price"] else "") + label, callback_data=f"p:{p['id']}:all")
    kb.adjust(1)
    more = f" (показаны первые 10 из {len(found)})" if len(found) > 10 else ""
    await m.answer(f"🔎 Нашёл{more}:", reply_markup=kb.as_markup())


@customer_router.message(Command("search"))
async def c_search_cmd(m: Message):
    parts = m.text.split(maxsplit=1)
    if len(parts) == 2:
        await do_search(m, parts[1])
    else:
        await m.answer("🔎 Напишите название товара или артикул (например, «чипсы» или <code>A002</code>).")


@customer_router.message(F.text, ~F.text.startswith("/"))
async def c_by_text(m: Message):
    await do_search(m, m.text)


# ═════════════════════ БОТ ПРОДАВЦА ═════════════════════
def admin_order_text(o):
    """o — строка из таблицы orders."""
    items = json.loads(o["items_json"])
    lines = "\n".join(
        f"• {html.escape(i['name'])}"
        + (f" [{html.escape(i['sku'])}]" if i.get("sku") else "")
        + f" × {i['qty']}"
        for i in items
    )
    surcharged = any(i.get("base_price", i["price"]) != i["price"] for i in items)
    who = f'<a href="tg://user?id={o["user_id"]}">{html.escape(o["full_name"] or "покупатель")}</a>'
    if o["username"]:
        who += f" (@{html.escape(o['username'])})"
    room_line = (
        f"Выдача: <b>{html.escape(o['room'])}</b>"
        if o["room"]
        else "Комната выдачи: <i>не указана</i>"
    )
    return (
        f"{STATUS_ICONS[o['status']]} <b>Заказ #{o['id']}</b> — {STATUS_LABELS[o['status']]}\n"
        f"{lines}\n"
        f"Сумма: <b>{o['total']} ₽</b>"
        + (f" 🌙 (ночной тариф +{SURCHARGE_PERCENT}%)" if surcharged else "")
        + (f"\n🏷 Промокод {html.escape(o['promo_code'])}: −{o['discount']} ₽" if o["promo_code"] else "")
        + "\n"
        f"Оплата: {pay_line(o)}\n"
        f"{room_line}\n"
        f"Клиент: {who}"
    )


def admin_order_kb(o):
    oid = o["id"]
    kb = InlineKeyboardBuilder()
    if o["status"] in ACTIVE_STATUSES:
        if o["payment"] == "transfer" and o["pay_status"] != "paid":
            kb.button(text="💸 Оплата получена", callback_data=f"adm:paid:{oid}")
            if o["pay_status"] == "claimed":
                kb.button(text="🚫 Оплаты нет", callback_data=f"adm:nopay:{oid}")
        if o["status"] == "new":
            kb.button(text="📍 Собран — указать комнату", callback_data=f"adm:room:{oid}")
        else:
            kb.button(text="✅ Выдан", callback_data=f"adm:done:{oid}")
            kb.button(text="📍 Сменить комнату", callback_data=f"adm:room:{oid}")
    kb.button(text="🧾 Чек", callback_data=f"rcpt:{oid}")
    if o["status"] in ACTIVE_STATUSES:
        kb.button(text="❌ Отменить", callback_data=f"adm:cancel:{oid}")
    kb.adjust(1)
    return kb.as_markup()


# ── Чек по заказу (для продавца) ──
RECEIPT_WIDTH = 32
RECEIPT_PAY = {
    "transfer": {"unpaid": "перевод, ждём оплату", "claimed": "перевод, клиент сообщил об оплате",
                 "paid": "перевод, получена"},
    "cash": {"unpaid": "наличные при выдаче", "claimed": "наличные при выдаче",
             "paid": "наличные, получены"},
}


def _receipt_row(left, right, width=RECEIPT_WIDTH):
    """«слева ........ справа» ровно в width символов (не влезает — через один пробел)."""
    return left + " " * max(width - len(left) - len(right), 1) + right


def _receipt_wrap(text, indent="", width=RECEIPT_WIDTH):
    return textwrap.wrap(text, width, subsequent_indent=indent, break_long_words=True) or [""]


def receipt_body(o):
    """Чек по заказу обычным текстом (o — строка из orders). Внизу — блок только для продавца."""
    items = json.loads(o["items_json"])
    with db() as c:
        costs = {r["id"]: r["cost"] for r in c.execute("SELECT id, cost FROM products")}
    sep = "-" * RECEIPT_WIDTH
    try:
        when = datetime.strptime(o["created_at"], "%Y-%m-%d %H:%M:%S").strftime("%d.%m.%Y %H:%M")
    except (TypeError, ValueError):
        when = o["created_at"] or ""

    who = o["full_name"] or "покупатель"
    if o["username"]:
        who += f" (@{o['username']})"
    pay = RECEIPT_PAY.get(o["payment"], {}).get(o["pay_status"], PAY_LABELS.get(o["payment"], o["payment"]))

    out = [f"ЧЕК · ЗАКАЗ #{o['id']}".center(RECEIPT_WIDTH).rstrip(), when.center(RECEIPT_WIDTH).rstrip(), sep]
    out += _receipt_wrap(f"Клиент: {who}", "  ")
    out.append(f"ID клиента: {o['user_id']}")
    out += _receipt_wrap(f"Выдача: {o['room'] or 'не указана'}", "  ")
    out += _receipt_wrap(f"Оплата: {pay}", "  ")
    out.append(f"Статус: {STATUS_LABELS.get(o['status'], o['status'])}")
    out.append(sep)

    subtotal, cost_sum, unknown = 0, 0.0, []
    for i in items:
        name = i["name"] + (f" [{i['sku']}]" if i.get("sku") else "")
        out += _receipt_wrap(name, "  ")
        line = i["price"] * i["qty"]
        subtotal += line
        out.append(_receipt_row(f"  {i['qty']} × {rub(i['price'])}", rub(line)))
        cost = i.get("cost")
        if cost is None:
            cost = costs.get(i["id"])
        if cost is None:
            unknown.append(i["name"])
        else:
            cost_sum += cost * i["qty"]
    out.append(sep)
    if o["promo_code"] and (o["discount"] or 0):
        out.append(_receipt_row("Сумма", rub(subtotal)))
        out += _receipt_wrap(f"Промокод {o['promo_code']}", "  ")
        out.append(_receipt_row("  скидка", "−" + rub(o["discount"])))
    out.append(_receipt_row("ИТОГО", rub(o["total"])))
    if any(i.get("base_price", i["price"]) != i["price"] for i in items):
        out.append(f"(ночной тариф +{SURCHARGE_PERCENT}% в ценах)")

    if o["status"] != "cancelled":
        out += [sep, "Для продавца (клиенту не", "показывать):"]
        if unknown:
            out += _receipt_wrap("Закупка не указана: " + ", ".join(unknown) + " — прибыль не посчитать", "  ")
        else:
            out.append(_receipt_row("Закупка", rub(cost_sum)))
            out.append(_receipt_row("Прибыль", rub(o["total"] - cost_sum)))
    return "\n".join(out)


async def send_receipt(message: Message, oid):
    o = get_order(oid)
    if not o:
        await message.answer(f"Заказ #{oid} не найден.")
        return
    body = receipt_body(o)
    text = "<pre>" + html.escape(body) + "</pre>"
    if len(text) > 4000:  # лимит Telegram 4096 — длинный чек отдаём файлом
        await message.answer_document(
            BufferedInputFile(body.encode("utf-8"), filename=f"check_{oid}.txt"),
            caption=f"🧾 Чек по заказу #{oid}",
        )
    else:
        await message.answer(text)


async def tell_customer(user_id, text, kb=None):
    try:
        await bots["customer"].send_message(user_id, text, reply_markup=kb)
        return True
    except TelegramForbiddenError:
        mark_blocked(user_id)  # человек заблокировал бота
        logging.warning("Покупатель %s заблокировал бота", user_id)
    except Exception:
        logging.warning("Не удалось написать покупателю %s", user_id)
    return False


SELLER_HELP = (
    "🧾 <b>Бот продавца</b>\n"
    "Заказы приходят сюда. Оплату переводом подтверждаете кнопкой «Оплата получена».\n\n"
    "/orders — активные заказы (у каждого есть кнопка «🧾 Чек»)\n"
    "/receipt [№] — чек по заказу (без номера — последнего)\n"
    "/stats — статистика (ночь / 7 / 30 дней / всё время), с прибылью\n"
    "/suggestions — предложения покупателей\n"
    "/stock — товары, артикулы, остатки\n"
    "/setprice id цена [id цена …]\n"
    "/setstock id кол-во [id кол-во …]\n"
    "/setcost id закупка [id закупка …] — закупочная цена (для прибыли), можно 21.9\n"
    "(эти три команды можно слать несколькими строками в одном сообщении)\n"
    "/setdesc id описание  («-» чтобы убрать)\n"
    "/setphoto id — фото товара: отправьте фото с подписью «/setphoto id» "
    "(или /setphoto id ссылка, «-» — убрать)\n"
    "/setsku id артикул\n"
    "/setcat id категория  («-» чтобы убрать)\n"
    "/rename id название\n"
    "/add Название | цена | остаток | описание | категория\n"
    "/hide id и /show id — скрыть/показать товар в каталоге\n\n"
    "🔥 <b>Акции и промокоды</b>\n"
    "/sale id цена — акционная цена (или /sale id -20%, /sale id - чтобы снять)\n"
    "/newpromo КОД 10% [лимит] или /newpromo КОД 50 [лимит] — создать промокод\n"
    "/promos — список промокодов, /delpromo КОД — удалить\n\n"
    "📥 <b>Массовая загрузка</b>\n"
    "/template — образец файла, /export — выгрузить товары, /import — как загрузить\n"
    "(просто пришлите боту файл .csv или .xlsx)\n\n"
    "🕐 <b>Режим работы</b>\n"
    "/hours — показать, /hours 22:00 06:00 — задать, /hours off — круглосуточно\n"
    "/closeshop [сообщение] и /openshop — закрыть/открыть магазин вручную\n\n"
    "🧺 <b>Смена</b>\n"
    "/pick — сборочный лист (что собрать по новым заказам)\n"
    "/report — отчёт за ночь (он же приходит сам после смены)\n"
    "/backup — резервная копия сейчас (раз в сутки приходит сама), /restore — как восстановить\n"
    "/soldout hide|show — прятать или показывать закончившиеся товары\n\n"
    "👥 <b>Люди и общение</b>\n"
    "/users — кто запустил бота (новые, заказчики, приглашённые), выгрузка в CSV\n"
    "/broadcast — рассылка покупателям (текст + фото, выбор аудитории, предпросмотр)\n"
    "/tickets — обращения в поддержку (приходят сюда сами, отвечать — кнопкой «Ответить»)\n"
    "🔔 Подписчики на товар получают уведомление сами, когда вы пополняете остаток; "
    "сколько ждёт — в /stock и /soldout.\n"
    "🎁 «Приведи друга» работает автоматически (суммы — REF_* в .env).\n\n"
    "id везде можно заменить артикулом (A001) в /setphoto, /setcat, /sale.\n"
    "/cancel — отменить ввод комнаты"
)


def stock_text():
    with db() as c:
        rows = c.execute("SELECT * FROM products ORDER BY id").fetchall()
    lines = []
    subs = sub_counts()
    for r in rows:
        hidden = "" if r["active"] else " 🙈 скрыт"
        lines.append(
            f"{r['id']}. [{html.escape(r['sku'] or '-')}] {html.escape(r['name'])} — "
            f"{r['price']} ₽"
            + (f" (закупка {r['cost']:g})" if r["cost"] is not None else " (закупка не указана)")
            + f" · ост. {r['stock']}{hidden}"
            + (" ⛔" if r["stock"] <= 0 else "")
            + (f" · 🔔 ждут {subs[r['id']]}" if subs.get(r["id"]) else "")
            + (f" · 🔥 акция {r['sale_price']} ₽" if r["sale_price"] else "")
            + (f" · 🗂 {html.escape(r['category'])}" if r["category"] else "")
            + ("" if (r["photo"] or r["photo_fid"]) else " 📷—")
        )
    note = (
        f"\n\n🌙 Указаны обычные цены. С {SURCHARGE_FROM:02d}:00 до {SURCHARGE_TO:02d}:00 "
        f"покупатели видят +{SURCHARGE_PERCENT}%."
    )
    return "<b>Склад</b> (id. [артикул] название)\n" + "\n".join(lines) + note


async def send_orders(message: Message):
    with db() as c:
        rows = c.execute(
            "SELECT * FROM orders WHERE status IN ('new','ready') ORDER BY id"
        ).fetchall()
    if not rows:
        await message.answer("Активных заказов нет 👍")
        return
    for o in rows:
        await message.answer(admin_order_text(o), reply_markup=admin_order_kb(o))


def panel_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="📋 Заказы", callback_data="s:orders")
    kb.button(text="📈 Статистика", callback_data="s:stats")
    kb.button(text="📦 Склад", callback_data="s:stock")
    kb.button(text="💡 Предложения", callback_data="s:sug")
    kb.button(text="🧺 Сборка", callback_data="s:pick")
    kb.button(text="👥 Пользователи", callback_data="s:users")
    kb.button(text="🆘 Обращения", callback_data="s:tickets")
    kb.adjust(2)
    return kb.as_markup()


@seller_router.message(CommandStart())
@seller_router.message(Command("help"))
async def s_start(m: Message, state: FSMContext):
    await state.clear()
    await setup_seller_commands(m.bot)
    await m.answer(SELLER_HELP, reply_markup=panel_kb())


@seller_router.message(Command("cancel"))
async def s_cancel(m: Message, state: FSMContext):
    await state.clear()
    await m.answer("Отменено.")


@seller_router.callback_query(F.data.in_({"s:orders", "s:stock", "s:stats", "s:sug", "s:pick", "s:users", "s:tickets"}))
async def s_panel(cb: CallbackQuery):
    if cb.data == "s:orders":
        await send_orders(cb.message)
    elif cb.data == "s:stock":
        await cb.message.answer(stock_text())
    elif cb.data == "s:stats":
        await cb.message.answer(stats_text("night"), reply_markup=stats_kb("night"))
    elif cb.data == "s:pick":
        await cb.message.answer(pick_list_text())
    elif cb.data == "s:users":
        await cb.message.answer(users_summary_text(), reply_markup=users_kb())
    elif cb.data == "s:tickets":
        await send_tickets(cb.message)
    else:
        await send_suggestions(cb.message)
    await cb.answer()


@seller_router.callback_query(F.data.startswith("adm:"))
async def s_order_action(cb: CallbackQuery, state: FSMContext):
    _, action, oid = cb.data.split(":")
    oid = int(oid)
    o = get_order(oid)
    if not o:
        await cb.answer("Заказ не найден", show_alert=True)
        return
    if o["status"] not in ACTIVE_STATUSES:
        await cb.answer("Заказ уже обработан", show_alert=True)
        return

    if action == "room":
        await state.set_state(AdminRoom.room)
        await state.update_data(oid=oid, msg_id=cb.message.message_id)
        await cb.message.answer(
            f"📍 Заказ #{oid}: напишите, в какой комнате его забрать "
            "(например «412» или «412, стучать 2 раза»).\nОтмена — /cancel"
        )
        await cb.answer()
        return

    note, alert, refund = None, None, False
    with db() as c:
        if action == "paid":
            c.execute("UPDATE orders SET pay_status='paid' WHERE id=?", (oid,))
            note = f"✅ Оплата заказа #{oid} подтверждена. Спасибо!"
        elif action == "nopay":
            c.execute("UPDATE orders SET pay_status='unpaid', reminded=2 WHERE id=?", (oid,))
            note = (
                f"⚠️ Оплата заказа #{oid} пока не найдена. Проверьте перевод и нажмите "
                "«Я оплатил(а)» ещё раз (/myorders) или напишите продавцу."
            )
        elif action == "done":
            if o["payment"] == "transfer" and o["pay_status"] != "paid":
                alert = "Сначала подтвердите оплату переводом (кнопка «Оплата получена»)."
            else:
                c.execute(
                    "UPDATE orders SET status='done', pay_status='paid' WHERE id=?", (oid,)
                )
                note = f"🤝 Заказ #{oid} выдан. Приятного аппетита!"
        elif action == "cancel":
            release_order(c, o)
            c.execute("UPDATE orders SET status='cancelled' WHERE id=?", (oid,))
            refund = o["payment"] == "transfer" and o["pay_status"] == "paid"
            note = f"Заказ #{oid} отменён. Если это ошибка — напишите продавцу."
        else:
            alert = "Неизвестное действие"

    if alert:
        await cb.answer(alert, show_alert=True)
        return
    o2 = get_order(oid)
    await safe_edit(cb.message, admin_order_text(o2), admin_order_kb(o2))
    await cb.answer("Готово ✅")
    if note:
        await tell_customer(o["user_id"], note)
    if refund:
        await cb.message.answer(f"⚠️ Заказ #{oid} был оплачен — верните {o['total']} ₽ покупателю.")
    if action == "done":
        res = referral_reward(o)
        if res:
            rid, code = res
            await tell_customer(
                rid,
                f"🎉 Ваш друг сделал первый заказ! Подарок вам: промокод <code>{code}</code> — "
                f"<b>−{REF_REWARD_AMOUNT} ₽</b> на любой заказ (/promo {code}).",
            )
            await cb.message.answer(f"🎁 «Приведи друга»: клиент {rid} получил промокод {code}.")


@seller_router.callback_query(F.data.startswith("rcpt:"))
async def s_receipt_cb(cb: CallbackQuery):
    await send_receipt(cb.message, int(cb.data.split(":")[1]))
    await cb.answer()


@seller_router.message(Command("receipt", "check"))
async def s_receipt(m: Message):
    parts = (m.text or "").split(maxsplit=1)
    arg = parts[1].strip().lstrip("#") if len(parts) > 1 else ""
    if arg:
        if not arg.isdigit():
            await m.answer("Формат: /receipt 12 — чек заказа №12, или просто /receipt — чек последнего заказа.")
            return
        oid = int(arg)
    else:
        with db() as c:
            oid = c.execute("SELECT MAX(id) FROM orders").fetchone()[0]
        if not oid:
            await m.answer("Заказов пока нет.")
            return
    await send_receipt(m, oid)


# ── Склад и товары ──
@seller_router.message(Command("stock"))
async def s_stock(m: Message):
    await m.answer(stock_text())


@seller_router.message(Command("orders"))
async def s_orders(m: Message):
    await send_orders(m)


# ═══ BULK BEGIN ═══
def parse_num(token, as_float):
    if as_float:
        try:
            v = float(token.replace(",", "."))
        except ValueError:
            return None
        return v if v >= 0 else None
    return int(token) if token.isdigit() else None


def apply_bulk(text):
    """Разбирает сообщение с несколькими командами /setprice, /setstock, /setcost.
    Каждая команда — с новой строки; после команды можно писать несколько пар
    «id значение». Строка без команды продолжает предыдущую команду.
    Возвращает список строк-отчётов."""
    columns = {
        "/setprice": ("price", False),
        "/setstock": ("stock", False),
        "/setcost": ("cost", True),  # закупка может быть дробной: 21.9
    }
    current = None
    report = []
    with db() as c:
        for raw in text.splitlines():
            parts = raw.split()
            if not parts:
                continue
            if parts[0].startswith("/"):
                cmd = parts[0].split("@")[0].lower()
                if cmd not in columns:
                    report.append(f"⚠️ «{html.escape(raw.strip())}»: неизвестная команда")
                    continue
                current = cmd
                parts = parts[1:]
            if current is None:
                continue
            column, as_float = columns[current]  # не пользовательский ввод
            pairs = []
            ok = bool(parts) and len(parts) % 2 == 0
            if ok:
                for i in range(0, len(parts), 2):
                    pid = int(parts[i]) if parts[i].isdigit() else None
                    val = parse_num(parts[i + 1], as_float)
                    if pid is None or val is None:
                        ok = False
                        break
                    pairs.append((pid, val))
            if not ok:
                report.append(
                    f"⚠️ «{html.escape(raw.strip())}»: нужен формат «id значение» (парами)"
                )
                continue
            for pid, val in pairs:
                row = c.execute("SELECT name FROM products WHERE id=?", (pid,)).fetchone()
                if not row:
                    report.append(f"⚠️ нет товара с id {pid}")
                    continue
                c.execute(f"UPDATE products SET {column}=? WHERE id=?", (val, pid))
                name = html.escape(row["name"])
                if column == "price":
                    report.append(f"✅ {name}: цена {val} ₽")
                elif column == "stock":
                    report.append(f"✅ {name}: остаток {val} шт.")
                else:
                    report.append(f"✅ {name}: закупка {val:g} ₽")
    return report
# ═══ BULK END ═══


@seller_router.message(Command("setstock", "setprice", "setcost"))
async def s_bulk_set(m: Message):
    report = apply_bulk(m.text)
    if not report:
        report = [
            "Формат (можно сразу несколько строк):\n"
            "/setprice 2 40\n/setprice 3 40\n/setstock 4 5\n/setcost 2 21.9\n\n"
            "или несколько пар в одной строке: /setprice 2 40 3 40 4 60"
        ]
    await m.answer("\n".join(report))


@seller_router.message(Command("setdesc"))
async def s_setdesc(m: Message):
    parts = m.text.split(maxsplit=2)
    if len(parts) != 3 or not parts[1].isdigit():
        await m.answer("Формат: /setdesc id описание\n(«-» вместо описания — убрать его)")
        return
    desc = "" if parts[2].strip() == "-" else parts[2].strip()[:600]
    with db() as c:
        cur = c.execute("UPDATE products SET description=? WHERE id=?", (desc, int(parts[1])))
    await m.answer("Готово ✅" if cur.rowcount else "Нет товара с таким id")


@seller_router.message(Command("setphoto"))
async def s_setphoto(m: Message):
    parts = (m.text or m.caption or "").split(maxsplit=2)
    if len(parts) < 2:
        await m.answer(
            "Фото товара: отправьте картинку с подписью «/setphoto id» (id или артикул смотрите в /stock).\n"
            "Или ссылкой: /setphoto id https://...jpg\n«/setphoto id -» — убрать фото."
        )
        return
    pid = find_pid(parts[1])
    if pid is None:
        await m.answer("Нет товара с таким id или артикулом")
        return
    arg = parts[2].strip() if len(parts) > 2 else ""
    photo = m.photo or (m.reply_to_message.photo if m.reply_to_message else None)
    if photo:
        # file_id привязан к боту, поэтому сохраняем сам файл и потом отправляем его из бота покупателя
        os.makedirs(PHOTOS_DIR, exist_ok=True)
        fname = f"p{pid}_{int(datetime.now().timestamp())}.jpg"
        await m.bot.download(photo[-1], destination=os.path.join(PHOTOS_DIR, fname))
        value = fname
    elif arg == "-":
        value = None
    elif arg.lower().startswith(("http://", "https://")):
        value = arg
    else:
        await m.answer("Пришлите фото с подписью «/setphoto id» или ссылку на картинку.")
        return
    with db() as c:
        c.execute("UPDATE products SET photo=?, photo_fid=NULL WHERE id=?", (value, pid))
    await m.answer("Фото убрано ✅" if value is None else "Фото сохранено ✅")


@seller_router.message(Command("setsku"))
async def s_setsku(m: Message):
    parts = m.text.split()
    if len(parts) != 3 or not parts[1].isdigit() or not SKU_RE.match(parts[2]):
        await m.answer(
            "Формат: /setsku id артикул\n"
            "Артикул — до 20 символов: буквы, цифры, «-» и «_» (например ROLL-CH)."
        )
        return
    try:
        with db() as c:
            cur = c.execute("UPDATE products SET sku=? WHERE id=?", (parts[2], int(parts[1])))
    except sqlite3.IntegrityError:
        await m.answer("Такой артикул уже есть у другого товара.")
        return
    await m.answer("Готово ✅" if cur.rowcount else "Нет товара с таким id")


@seller_router.message(Command("rename"))
async def s_rename(m: Message):
    parts = m.text.split(maxsplit=2)
    if len(parts) != 3 or not parts[1].isdigit() or not parts[2].strip():
        await m.answer("Формат: /rename id Новое название")
        return
    name = parts[2].strip()[:80]
    with db() as c:
        cur = c.execute("UPDATE products SET name=? WHERE id=?", (name, int(parts[1])))
    await m.answer(f"Готово ✅ {html.escape(name)}" if cur.rowcount else "Нет товара с таким id")


@seller_router.message(Command("add"))
async def s_add(m: Message):
    raw = m.text.partition(" ")[2]
    f = [x.strip() for x in raw.split("|")]
    if len(f) < 3 or not f[0] or not f[1].isdigit() or not f[2].isdigit():
        await m.answer(
            "Формат: /add Название | цена | остаток | описание | категория (последние два можно не писать)\n"
            "Например: /add Сникерс | 70 | 10 | Шоколадный батончик | Снеки"
        )
        return
    desc = f[3][:600] if len(f) > 3 else ""
    cat = f[4][:30] if len(f) > 4 else ""
    with db() as c:
        cur = c.execute(
            "INSERT INTO products(name, price, stock, description, category) VALUES(?,?,?,?,?)",
            (f[0][:80], int(f[1]), int(f[2]), desc, cat),
        )
        sku = make_sku(c, cur.lastrowid)
        c.execute("UPDATE products SET sku=? WHERE id=?", (sku, cur.lastrowid))
    await m.answer(
        f"Добавлено ✅ id {cur.lastrowid}, артикул <code>{html.escape(sku)}</code>: "
        f"{html.escape(f[0])}"
    )


@seller_router.message(Command("hide", "show"))
async def s_hide_show(m: Message):
    parts = m.text.split()
    if len(parts) != 2 or not parts[1].isdigit():
        await m.answer("Формат: /hide id  или  /show id")
        return
    active = 0 if parts[0].lstrip("/").split("@")[0].lower() == "hide" else 1
    with db() as c:
        cur = c.execute("UPDATE products SET active=? WHERE id=?", (active, int(parts[1])))
    if not cur.rowcount:
        await m.answer("Нет товара с таким id")
    else:
        await m.answer("Скрыт 🙈" if not active else "Показан 👀")


# ── Сборочный лист ──
def pick_list_text():
    """Что собрать прямо сейчас: заказы со статусом «принят» (ещё не собраны)."""
    with db() as c:
        orders = c.execute("SELECT * FROM orders WHERE status='new' ORDER BY id").fetchall()
    if not orders:
        return "🧺 Собирать нечего: новых заказов нет 👍"
    with db() as c:
        cur_prod = {r["id"]: r for r in c.execute("SELECT id, name, sku FROM products").fetchall()}
    totals, per_order = {}, []
    for o in orders:
        parts = []
        for i in json.loads(o["items_json"]):
            p = cur_prod.get(i["id"])  # группируем по товару (в старых заказах артикула нет)
            key = (i["id"], p["name"] if p else i["name"], (p["sku"] if p else i.get("sku")) or "-")
            totals[key] = totals.get(key, 0) + i["qty"]
            parts.append(f"{html.escape(i['name'])} × {i['qty']}")
        who = html.escape(o["full_name"] or "покупатель")
        if o["username"]:
            who += f" (@{html.escape(o['username'])})"
        if o["payment"] == "cash":
            pay = "💵 наличные"
        else:
            pay = {"unpaid": "⏳ не оплачен", "claimed": "🔔 говорит, что оплатил", "paid": "✅ оплачен"}[o["pay_status"]]
        per_order.append(f"<b>#{o['id']}</b> · {who} · {pay} · {o['total']} ₽\n    " + "; ".join(parts))
    lines = [f"🧺 <b>Сборочный лист</b> — заказов: {len(orders)}", "", "<b>Всего собрать:</b>"]
    for (_, name, sku), qty in sorted(totals.items(), key=lambda kv: kv[0][1].casefold()):
        lines.append(f"☐ {html.escape(name)} [{html.escape(sku)}] — <b>{qty} шт.</b>")
    lines += ["", "<b>По заказам:</b>"] + per_order
    lines.append("\nУказать комнату и отметить собранным — в /orders.")
    return "\n".join(lines)


@seller_router.message(Command("pick"))
async def s_pick(m: Message):
    await m.answer(pick_list_text())


# ── Отчёт, резервная копия, закончившиеся товары ──
@seller_router.message(Command("report"))
async def s_report(m: Message):
    await m.answer("🌅 <b>Отчёт</b>\n\n" + stats_text("night"), reply_markup=stats_kb("night"))


async def send_backup(bot, caption_prefix="💾 Резервная копия"):
    data, fname, with_photos = make_backup()
    await bot.send_document(
        ADMIN_ID,
        BufferedInputFile(data, filename=fname),
        caption=(
            f"{caption_prefix}: база + {'фото товаров' if with_photos else 'без фото'}.\n"
            "Восстановить: отправьте этот файл боту с подписью /restore"
        ),
    )


@seller_router.message(Command("backup"))
async def s_backup(m: Message):
    try:
        await send_backup(m.bot)
    except ValueError as e:
        await m.answer(f"⚠️ {html.escape(str(e))}")


@seller_router.message(Command("restore"))
async def s_restore_help(m: Message):
    await m.answer(
        "♻️ Восстановление из копии: отправьте боту файл копии (.zip из /backup или .db) "
        "и в подписи к файлу напишите /restore.\n"
        "Текущая база перед этим автоматически сохранится и придёт вам файлом."
    )


@seller_router.message(Command("soldout"))
async def s_soldout(m: Message):
    parts = m.text.split()
    if len(parts) == 2 and parts[1].lower() in ("hide", "show"):
        set_setting("soldout_mode", parts[1].lower())
    mode = get_setting("soldout_mode", "hide")
    await m.answer(
        "Закончившиеся товары: "
        + ("🙈 скрываются из каталога, сами вернутся при пополнении остатка" if mode == "hide"
           else "👀 показываются внизу списка с пометкой «нет в наличии»")
        + "\n\nПереключить: /soldout hide или /soldout show"
        + soldout_list_text()
    )


# ── Категории и акции ──
@seller_router.message(Command("setcat"))
async def s_setcat(m: Message):
    parts = m.text.split(maxsplit=2)
    pid = find_pid(parts[1]) if len(parts) == 3 else None
    if len(parts) != 3:
        await m.answer("Формат: /setcat id категория\n(«-» вместо категории — убрать). Например: /setcat A003 Снеки")
        return
    if pid is None:
        await m.answer("Нет товара с таким id или артикулом")
        return
    cat = "" if parts[2].strip() == "-" else parts[2].strip()[:30]
    with db() as c:
        c.execute("UPDATE products SET category=? WHERE id=?", (cat, pid))
    await m.answer(f"Категория: {html.escape(cat)} ✅" if cat else "Категория убрана ✅")


@seller_router.message(Command("sale"))
async def s_sale(m: Message):
    parts = m.text.split()
    usage = (
        "Формат: /sale id цена — акционная цена в рублях\n"
        "или /sale id -20% — скидка в процентах\n"
        "или /sale id - — снять акцию.\n"
        "id можно заменить артикулом, например: /sale A001 120"
    )
    if len(parts) != 3:
        await m.answer(usage)
        return
    pid = find_pid(parts[1])
    if pid is None:
        await m.answer("Нет товара с таким id или артикулом")
        return
    with db() as c:
        p = c.execute("SELECT name, price FROM products WHERE id=?", (pid,)).fetchone()
        val = parts[2]
        if val == "-":
            c.execute("UPDATE products SET sale_price=NULL WHERE id=?", (pid,))
            await m.answer(f"Акция снята: {html.escape(p['name'])} ✅")
            return
        if val.endswith("%") and val[:-1].lstrip("-").isdigit():
            pct = int(val[:-1].lstrip("-"))
            sale = (p["price"] * (100 - pct) + 50) // 100 if 1 <= pct <= 90 else 0
        elif val.isdigit():
            sale = int(val)
        else:
            await m.answer(usage)
            return
        if not (0 < sale < p["price"]):
            await m.answer(f"Акционная цена должна быть больше 0 и меньше обычной ({p['price']} ₽). Для процентов — от 1% до 90%.")
            return
        c.execute("UPDATE products SET sale_price=? WHERE id=?", (sale, pid))
    await m.answer(f"🔥 Акция: {html.escape(p['name'])} — было {p['price']} ₽, стало <b>{sale} ₽</b>")


# ── Промокоды ──
@seller_router.message(Command("newpromo"))
async def s_newpromo(m: Message):
    parts = m.text.split()
    ok = len(parts) in (3, 4) and PROMO_RE.match(parts[1])
    percent = amount = 0
    if ok:
        d = parts[2]
        if d.endswith("%") and d[:-1].isdigit() and 1 <= int(d[:-1]) <= 90:
            percent = int(d[:-1])
        elif d.isdigit() and int(d) > 0:
            amount = int(d)
        else:
            ok = False
    limit = None
    if ok and len(parts) == 4:
        if parts[3].isdigit() and int(parts[3]) > 0:
            limit = int(parts[3])
        else:
            ok = False
    if not ok:
        await m.answer(
            "Формат: /newpromo КОД скидка [лимит]\n"
            "Скидка: 10% (от 1 до 90) или сумма в рублях, например 50.\n"
            "Лимит — сколько раз можно использовать всего (по одному разу на человека).\n"
            "Например: /newpromo NIGHT10 10% 30   или   /newpromo WELCOME 50"
        )
        return
    code = parts[1].upper()
    with db() as c:
        c.execute(
            "INSERT INTO promocodes(code, percent, amount, max_uses) VALUES(?,?,?,?) "
            "ON CONFLICT(code) DO UPDATE SET percent=excluded.percent, amount=excluded.amount, "
            "max_uses=excluded.max_uses",
            (code, percent, amount, limit),
        )
    await m.answer(
        f"🏷 Промокод <code>{code}</code>: скидка "
        + (f"{percent}%" if percent else f"{amount} ₽")
        + (f", лимит {limit}" if limit else ", без лимита")
        + "\nПокупатель вводит его в корзине или командой /promo."
    )


@seller_router.message(Command("promos"))
async def s_promos(m: Message):
    with db() as c:
        rows = c.execute("SELECT * FROM promocodes WHERE owner_id IS NULL ORDER BY code").fetchall()
        personal = c.execute("SELECT COUNT(*) FROM promocodes WHERE owner_id IS NOT NULL").fetchone()[0]
    if not rows:
        await m.answer(
            "Промокодов нет. Создать: /newpromo КОД 10% [лимит]"
            + (f"\n(личных кодов «Приведи друга»: {personal})" if personal else "")
        )
        return
    lines = [
        f"<code>{r['code']}</code> — "
        + (f"{r['percent']}%" if r["percent"] else f"{r['amount']} ₽")
        + f" · использован {r['used']}"
        + (f" из {r['max_uses']}" if r["max_uses"] else " раз")
        for r in rows
    ]
    await m.answer(
        "🏷 <b>Промокоды</b>\n" + "\n".join(lines)
        + (f"\n\n🎁 Личных кодов «Приведи друга»: {personal} (в список не входят)" if personal else "")
        + "\n\nУдалить: /delpromo КОД"
    )


@seller_router.message(Command("delpromo"))
async def s_delpromo(m: Message):
    parts = m.text.split()
    if len(parts) != 2:
        await m.answer("Формат: /delpromo КОД")
        return
    with db() as c:
        cur = c.execute("DELETE FROM promocodes WHERE code=?", (parts[1].upper(),))
        c.execute("DELETE FROM cart_promos WHERE code=?", (parts[1].upper(),))
    await m.answer("Удалён ✅" if cur.rowcount else "Такого промокода нет")


# ── Режим работы ──
@seller_router.message(Command("hours"))
async def s_hours(m: Message):
    parts = m.text.split()
    if len(parts) == 2 and parts[1].lower() in ("off", "24/7", "круглосуточно"):
        set_setting("work_from", "")
        set_setting("work_to", "")
    elif len(parts) == 3:
        a, b = parse_hhmm(parts[1]), parse_hhmm(parts[2])
        if a is None or b is None or a == b:
            await m.answer("Формат: /hours 22:00 06:00 (время открытия и закрытия)")
            return
        set_setting("work_from", fmt_min(a))
        set_setting("work_to", fmt_min(b))
    elif len(parts) != 1:
        await m.answer("Формат: /hours 22:00 06:00  или  /hours off  (круглосуточно)")
        return
    _, status = shop_status()
    await m.answer(
        f"🕐 Режим работы: {schedule_text()}\nСейчас для покупателей: {status}\n\n"
        "Задать: /hours 22:00 06:00 · круглосуточно: /hours off\n"
        "Закрыть вручную: /closeshop · открыть: /openshop"
    )


@seller_router.message(Command("closeshop"))
async def s_closeshop(m: Message):
    msg = m.text.partition(" ")[2].strip()[:200]
    set_setting("manual_closed", "1")
    set_setting("closed_msg", msg or None)
    await m.answer(
        "🔴 Магазин закрыт: новые заказы не принимаются (уже оформленные — в работе).\n"
        "Открыть снова: /openshop"
    )


@seller_router.message(Command("openshop"))
async def s_openshop(m: Message):
    set_setting("manual_closed", None)
    set_setting("closed_msg", None)
    _, status = shop_status()
    await m.answer(f"Готово ✅ Сейчас для покупателей: {status}")


# ═══ IMPORT BEGIN ═══ Массовая загрузка товаров из CSV / XLSX ═══
EXPORT_HEADERS = ["Артикул", "Название", "Цена", "Остаток", "Закупка", "Категория", "Акция", "Описание"]
IMPORT_ALIASES = {
    "sku": ("артикул", "sku"),
    "name": ("название", "наименование", "товар", "name"),
    "price": ("цена", "price"),
    "stock": ("остаток", "количество", "кол-во", "stock", "qty"),
    "cost": ("закупка", "закупочная", "закупочная цена", "себестоимость", "cost"),
    "category": ("категория", "category"),
    "sale": ("акция", "цена по акции", "акционная цена", "sale"),
    "description": ("описание", "description"),
}
IMPORT_MAX_ROWS = 500


def table_to_csv_bytes(rows):
    buf = io.StringIO()
    w = csv.writer(buf, delimiter=";")
    w.writerow(EXPORT_HEADERS)
    w.writerows(rows)
    return buf.getvalue().encode("utf-8-sig")  # BOM — Excel сразу видит кириллицу


def read_table(filename, data):
    """Строки таблицы (списки строк) из .csv/.txt/.xlsx."""
    name = (filename or "").lower()
    if name.endswith(".xlsx"):
        try:
            import openpyxl
        except ImportError:
            raise ValueError("Для .xlsx нужна библиотека openpyxl (pip install openpyxl). Либо пришлите CSV.")
        wb = openpyxl.load_workbook(io.BytesIO(data), read_only=True, data_only=True)
        ws = wb.active
        if ws is None:
            raise ValueError("В файле нет листов.")
        rows = [["" if v is None else str(v).strip() for v in r] for r in ws.iter_rows(values_only=True)]
    elif name.endswith((".csv", ".txt")):
        for enc in ("utf-8-sig", "cp1251"):
            try:
                text = data.decode(enc)
                break
            except UnicodeDecodeError:
                continue
        else:
            raise ValueError("Не удалось прочитать кодировку файла. Сохраните CSV в UTF-8.")
        first = text.splitlines()[0] if text.strip() else ""
        delim = max((";", ",", "\t"), key=first.count)
        rows = [[x.strip() for x in r] for r in csv.reader(io.StringIO(text), delimiter=delim)]
    else:
        raise ValueError("Нужен файл .csv или .xlsx")
    rows = [r for r in rows if any(r)]
    if len(rows) < 2:
        raise ValueError("В файле нет данных: нужна строка заголовков и хотя бы один товар.")
    if len(rows) > IMPORT_MAX_ROWS + 1:
        raise ValueError(f"Слишком много строк (максимум {IMPORT_MAX_ROWS}).")
    return rows


def _num(s, integer=True):
    s = s.replace(" ", "").replace("\u00a0", "").replace("₽", "").replace(",", ".")
    v = float(s)
    if v < 0:
        raise ValueError
    if integer:
        if v != int(v):
            raise ValueError
        return int(v)
    return v


def import_products(rows):
    """Добавляет новые и обновляет существующие товары (по артикулу, иначе по названию).
    Пустая ячейка = «не менять». Возвращает (добавлено, обновлено, ошибки)."""
    idx = {}
    for n, h in enumerate(rows[0]):
        key = h.casefold().strip()
        for field, names in IMPORT_ALIASES.items():
            if key in names and field not in idx:
                idx[field] = n
    if "name" not in idx:
        raise ValueError("Не нашёл колонку «Название» в первой строке файла. Образец: /template")
    added = updated = 0
    errors = []
    with db() as c:
        by_sku, by_name, by_name_of = {}, {}, {}
        for r in c.execute("SELECT id, name, sku FROM products").fetchall():
            by_sku[(r["sku"] or "").casefold()] = r["id"]
            by_name[r["name"].casefold()] = r["id"]
            by_name_of[r["id"]] = r["name"]
        for ln, row in enumerate(rows[1:], start=2):
            def cell(f):
                i = idx.get(f)
                return row[i].strip() if i is not None and i < len(row) else ""

            name = cell("name")[:80]
            if not name and cell("sku") and cell("sku").casefold() in by_sku:
                name = by_name_of[by_sku[cell("sku").casefold()]]  # только артикул — обновляем по нему
            if not name:
                errors.append(f"строка {ln}: пустое название")
                continue
            try:
                price = _num(cell("price")) if cell("price") else None
                stock = _num(cell("stock")) if cell("stock") else None
                cost = _num(cell("cost"), False) if cell("cost") else None
                sale_raw = cell("sale")
                sale = None if sale_raw in ("", "-", "0") else _num(sale_raw)
            except ValueError:
                errors.append(f"строка {ln} ({name}): в числовой колонке не число")
                continue
            sku = cell("sku")
            if sku and not SKU_RE.match(sku):
                errors.append(f"строка {ln} ({name}): артикул — до 20 символов: буквы, цифры, «-», «_»")
                continue
            category, desc = cell("category")[:30], cell("description")[:600]
            pid = by_sku.get(sku.casefold()) if sku else None
            by_sku_match = pid is not None
            if pid is None:
                pid = by_name.get(name.casefold())
            if pid is not None:
                cur_row = c.execute("SELECT price, sku FROM products WHERE id=?", (pid,)).fetchone()
                eff_base = price if price is not None else cur_row["price"]
                if sale is not None and not (0 < sale < eff_base):
                    errors.append(f"строка {ln} ({name}): акция должна быть меньше цены ({eff_base} ₽)")
                    continue
                sets, vals = [], []
                if by_sku_match:
                    sets.append("name=?"); vals.append(name)
                elif sku and sku.casefold() != (cur_row["sku"] or "").casefold():
                    sets.append("sku=?"); vals.append(sku)
                    by_sku[sku.casefold()] = pid
                for col, v in (("price", price), ("stock", stock), ("cost", cost),
                               ("category", category or None), ("description", desc or None)):
                    if v is not None:
                        sets.append(f"{col}=?"); vals.append(v)
                if sale_raw in ("-", "0"):
                    sets.append("sale_price=NULL")
                elif sale is not None:
                    sets.append("sale_price=?"); vals.append(sale)
                if sets:
                    c.execute(f"UPDATE products SET {', '.join(sets)} WHERE id=?", (*vals, pid))
                by_name[name.casefold()] = pid
                updated += 1
            else:
                if price is None or price <= 0:
                    errors.append(f"строка {ln} ({name}): новому товару нужна цена")
                    continue
                if sale is not None and not (0 < sale < price):
                    errors.append(f"строка {ln} ({name}): акция должна быть меньше цены")
                    continue
                cur = c.execute(
                    "INSERT INTO products(name, price, stock, cost, description, category, sale_price) "
                    "VALUES(?,?,?,?,?,?,?)",
                    (name, price, stock or 0, cost, desc, category, sale),
                )
                new_sku = sku or make_sku(c, cur.lastrowid)
                c.execute("UPDATE products SET sku=? WHERE id=?", (new_sku, cur.lastrowid))
                by_sku[new_sku.casefold()] = cur.lastrowid
                by_name[name.casefold()] = cur.lastrowid
                added += 1
    return added, updated, errors
# ═══ IMPORT END ═══


@seller_router.message(Command("template"))
async def s_template(m: Message):
    sample = [
        ["", "Сникерс 50 г", 70, 10, 45, "Снеки", "", "Шоколадный батончик"],
        ["A001", "Добрый Кола без сахара 1,5 л", 150, 9, 107.7, "Напитки", 120, "Пустая ячейка = не менять"],
    ]
    await m.answer_document(
        BufferedInputFile(table_to_csv_bytes(sample), filename="shop_template.csv"),
        caption=(
            "📥 Образец. Заполните и пришлите мне этим же файлом (.csv или .xlsx).\n"
            "• Товар ищется по артикулу, а если его нет — по названию: найден → обновится, нет → добавится.\n"
            "• Пустая ячейка = «не менять». «Акция»: цена по акции, «-» — снять.\n"
            "• Нужны только «Название» (и «Цена» для новых товаров)."
        ),
    )


@seller_router.message(Command("export"))
async def s_export(m: Message):
    with db() as c:
        rows = c.execute("SELECT * FROM products ORDER BY id").fetchall()
    table = [
        [r["sku"], r["name"], r["price"], r["stock"], "" if r["cost"] is None else f"{r['cost']:g}",
         r["category"], r["sale_price"] or "", r["description"]]
        for r in rows
    ]
    await m.answer_document(
        BufferedInputFile(table_to_csv_bytes(table), filename="products.csv"),
        caption="📤 Все товары. Правьте и присылайте обратно — обновятся по артикулу.",
    )


@seller_router.message(Command("import"))
async def s_import_help(m: Message):
    await m.answer(
        "📥 Пришлите мне файл .csv или .xlsx с товарами (просто отправьте как документ).\n"
        "Образец — /template, текущие товары в таком же формате — /export."
    )


@seller_router.message(F.document)
async def s_import_file(m: Message):
    doc = m.document
    fname = (doc.file_name or "").lower()
    if fname.endswith((".db", ".zip")):
        if not (m.caption or "").strip().lower().startswith("/restore"):
            await m.answer("Это похоже на резервную копию. Чтобы восстановить из неё, отправьте файл ещё раз с подписью /restore.")
            return
        if doc.file_size and doc.file_size > 48 * 1024 * 1024:
            await m.answer("Файл слишком большой.")
            return
        try:
            buf = await m.bot.download(doc)
            data = buf.read()
            await send_backup(m.bot, "🛟 Копия ПЕРЕД восстановлением")  # страховка
            n, photos = restore_from_file(doc.file_name, data)
        except ValueError as e:
            await m.answer(f"⚠️ {html.escape(str(e))}")
            return
        except Exception:
            logging.exception("Ошибка восстановления")
            await m.answer("⚠️ Не получилось восстановить из файла. Текущая база не тронута.")
            return
        await m.answer(f"♻️ Восстановлено: товаров {n}, фото {photos}. Проверьте /stock и /orders.")
        return
    if doc.file_size and doc.file_size > 1_000_000:
        await m.answer("Файл слишком большой (максимум 1 МБ).")
        return
    try:
        buf = await m.bot.download(doc)
        rows = read_table(doc.file_name, buf.read())
        added, updated, errors = import_products(rows)
    except ValueError as e:
        await m.answer(f"⚠️ {html.escape(str(e))}")
        return
    except Exception:
        logging.exception("Ошибка импорта")
        await m.answer("⚠️ Не получилось прочитать файл. Проверьте формат (образец — /template).")
        return
    out = [f"📥 Готово: добавлено <b>{added}</b>, обновлено <b>{updated}</b>, ошибок <b>{len(errors)}</b>."]
    if errors:
        out.append("\n".join("⚠️ " + html.escape(e) for e in errors[:10]))
        if len(errors) > 10:
            out.append(f"…и ещё {len(errors) - 10}")
    out.append("Проверить: /stock")
    await m.answer("\n".join(out))


# ── Статистика ──
@seller_router.message(Command("stats"))
async def s_stats(m: Message):
    await m.answer(stats_text("night"), reply_markup=stats_kb("night"))


@seller_router.callback_query(F.data.startswith("st:"))
async def s_stats_cb(cb: CallbackQuery):
    key = cb.data.split(":")[1]
    if key not in ("night", "7", "30", "all"):
        await cb.answer()
        return
    await safe_edit(cb.message, stats_text(key), stats_kb(key))
    await cb.answer()


# ── Предложения ──
def sug_card_text(s):
    who = f'<a href="tg://user?id={s["user_id"]}">{html.escape(s["full_name"] or "покупатель")}</a>'
    if s["username"]:
        who += f" (@{html.escape(s['username'])})"
    return (
        f"{SUG_ICONS[s['status']]} <b>Предложение #{s['id']}</b> — 👍 {s['votes']}\n"
        f"{html.escape(s['text'])}\n"
        f"От: {who} · {s['created_at'][:16]}"
    )


def sug_kb(s):
    if s["status"] in ("done", "rejected"):
        return None
    kb = InlineKeyboardBuilder()
    if s["status"] == "new":
        kb.button(text="📌 В планы", callback_data=f"sga:plan:{s['id']}")
    kb.button(text="✅ Добавлено", callback_data=f"sga:done:{s['id']}")
    kb.button(text="🚫 Отклонить", callback_data=f"sga:rej:{s['id']}")
    kb.adjust(1)
    return kb.as_markup()


async def send_suggestions(message: Message):
    rows = active_suggestions(None, 10)
    if not rows:
        await message.answer("Новых идей нет 💡")
        return
    await message.answer(f"💡 <b>Предложения</b> — топ по голосам (показано {len(rows)})")
    for s in rows:
        await message.answer(sug_card_text(s), reply_markup=sug_kb(s))


@seller_router.message(Command("suggestions"))
async def s_suggestions(m: Message):
    await send_suggestions(m)


@seller_router.callback_query(F.data.startswith("sga:"))
async def s_sug_action(cb: CallbackQuery):
    _, action, sid = cb.data.split(":")
    status = {"plan": "planned", "done": "done", "rej": "rejected"}.get(action)
    s = get_suggestion(int(sid))
    if not s or not status:
        await cb.answer("Предложение не найдено", show_alert=True)
        return
    with db() as c:
        c.execute("UPDATE suggestions SET status=? WHERE id=?", (status, s["id"]))
    s2 = get_suggestion(s["id"])
    await safe_edit(cb.message, sug_card_text(s2), sug_kb(s2))
    await cb.answer("Готово ✅")
    short = html.escape(s["text"][:80])
    notes = {
        "planned": f"📌 Ваша идея «{short}» взята в планы. Спасибо!",
        "done": f"🎉 Ваша идея «{short}» реализована — загляните в /menu!",
        "rejected": f"Спасибо за идею «{short}». Пока добавить это не получится.",
    }
    await tell_customer(s["user_id"], notes[status])


# Последним среди сообщений продавца — чтобы команды срабатывали раньше него.
@seller_router.message(AdminRoom.room, F.text)
async def s_got_room(m: Message, state: FSMContext):
    room = m.text.strip()
    if not room or len(room) > 60:
        await m.answer("Напишите комнату коротким текстом (до 60 символов) или /cancel.")
        return
    data = await state.get_data()
    oid, msg_id = data.get("oid"), data.get("msg_id")
    await state.clear()

    with db() as c:
        o = c.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
        ok = o is not None and o["status"] in ACTIVE_STATUSES
        if ok:
            c.execute("UPDATE orders SET room=?, status='ready' WHERE id=?", (room, oid))
            o = c.execute("SELECT * FROM orders WHERE id=?", (oid,)).fetchone()
    if not ok:
        await m.answer("Этот заказ уже обработан.")
        return

    text, kb = admin_order_text(o), admin_order_kb(o)
    try:
        await m.bot.edit_message_text(text, chat_id=m.chat.id, message_id=msg_id, reply_markup=kb)
    except TelegramBadRequest:
        await m.answer(text, reply_markup=kb)
    await m.answer(f"Отправил покупателю: забирать в «{html.escape(room)}» ✅")

    msg = f"📦 <b>Заказ #{oid} собран!</b>\nЗабирайте здесь: <b>{html.escape(room)}</b>"
    if o["payment"] == "transfer" and o["pay_status"] != "paid":
        msg += "\n\n💸 Оплата ещё не подтверждена: переведите сумму и нажмите «Я оплатил(а)» (/myorders)."
    await tell_customer(o["user_id"], msg)


# ── Пользователи, обращения, рассылка ──
def users_kb():
    kb = InlineKeyboardBuilder()
    kb.button(text="📥 Выгрузить список (CSV)", callback_data="us:csv")
    kb.button(text="📣 Сделать рассылку", callback_data="us:bc")
    kb.adjust(1)
    return kb.as_markup()


@seller_router.message(Command("users"))
async def s_users(m: Message):
    await m.answer(users_summary_text(), reply_markup=users_kb())


@seller_router.callback_query(F.data == "us:csv")
async def s_users_csv(cb: CallbackQuery):
    await cb.message.answer_document(
        BufferedInputFile(users_csv_bytes(), filename=f"users_{datetime.now(ZoneInfo(TZ)):%Y%m%d}.csv"),
        caption="👥 Все, кто запускал бота. Откройте в Excel.",
    )
    await cb.answer()


@seller_router.callback_query(F.data == "us:bc")
async def s_users_bc(cb: CallbackQuery, state: FSMContext):
    await start_broadcast(cb.message, state)
    await cb.answer()


async def send_tickets(message: Message):
    with db() as c:
        rows = c.execute(
            """SELECT t.*,
                      (SELECT text FROM ticket_msgs WHERE ticket_id=t.id ORDER BY id DESC LIMIT 1) AS last_text,
                      (SELECT from_seller FROM ticket_msgs WHERE ticket_id=t.id ORDER BY id DESC LIMIT 1) AS last_seller
               FROM tickets t WHERE t.status='open' ORDER BY t.updated_at DESC LIMIT 10"""
        ).fetchall()
    if not rows:
        await message.answer("Открытых обращений нет 👍")
        return
    for t in rows:
        who = html.escape(t["full_name"] or "покупатель")
        if t["username"]:
            who += f" (@{html.escape(t['username'])})"
        wait = "" if t["last_seller"] else " — <b>ждёт ответа</b>"
        last = html.escape((t["last_text"] or "📷 фото")[:200])
        await message.answer(
            f"🆘 <b>#{t['id']}</b> · {who} · {t['updated_at'][5:16]}{wait}\n«{last}»",
            reply_markup=ticket_kb(t["id"]),
        )


@seller_router.message(Command("tickets"))
async def s_tickets(m: Message):
    await send_tickets(m)


@seller_router.callback_query(F.data.startswith("tk:r:"))
async def s_ticket_reply_start(cb: CallbackQuery, state: FSMContext):
    tid = int(cb.data.split(":")[2])
    if not get_ticket(tid):
        await cb.answer("Обращение не найдено", show_alert=True)
        return
    await state.set_state(SupportReply.text)
    await state.update_data(tid=tid)
    await cb.message.answer(f"✉️ Ответ клиенту по обращению #{tid}: напишите текст (можно с фото).\nОтмена — /cancel")
    await cb.answer()


@seller_router.callback_query(F.data.startswith("tk:c:"))
async def s_ticket_close(cb: CallbackQuery):
    tid = int(cb.data.split(":")[2])
    t = get_ticket(tid)
    if not t:
        await cb.answer("Обращение не найдено", show_alert=True)
        return
    if t["status"] == "open":
        close_ticket(tid)
        await tell_customer(
            t["user_id"], f"✅ Обращение #{tid} закрыто. Если вопрос остался — напишите снова: /support"
        )
    try:
        await cb.message.edit_reply_markup(reply_markup=None)
    except TelegramBadRequest:
        pass
    await cb.answer("Закрыто ✅")


@seller_router.message(SupportReply.text, F.text | F.photo)
async def s_ticket_reply(m: Message, state: FSMContext):
    if m.text and m.text.startswith("/"):
        await m.answer("Напишите ответ обычным сообщением или нажмите /cancel.")
        return
    data = await state.get_data()
    t = get_ticket(data.get("tid"))
    if not t:
        await state.clear()
        await m.answer("Обращение не найдено.")
        return
    plain = (m.text or m.caption or "").strip()
    body = f"💬 <b>Поддержка</b> · обращение #{t['id']}\n\n{m.html_text if plain else ''}"
    kb = InlineKeyboardBuilder()
    kb.button(text="✍️ Ответить", callback_data=f"sup:more:{t['id']}")
    kb.button(text="✅ Вопрос решён", callback_data=f"sup:done:{t['id']}")
    kb.adjust(2)
    try:
        if m.photo:
            buf = await m.bot.download(m.photo[-1])
            await bots["customer"].send_photo(
                t["user_id"], BufferedInputFile(buf.read(), filename="photo.jpg"),
                caption=body[:1000], reply_markup=kb.as_markup(),
            )
        else:
            await bots["customer"].send_message(t["user_id"], body, reply_markup=kb.as_markup())
    except TelegramForbiddenError:
        mark_blocked(t["user_id"])
        await state.clear()
        await m.answer("⚠️ Клиент заблокировал бота — сообщение не доставлено.")
        return
    except Exception:
        logging.exception("Не удалось ответить клиенту")
        await m.answer("⚠️ Не получилось отправить ответ. Проверьте текст и попробуйте ещё раз.")
        return
    add_seller_msg(t["id"], plain, bool(m.photo))
    await state.clear()
    await m.answer(f"Отправлено клиенту ✅ (обращение #{t['id']} остаётся открытым — закройте его, когда всё решено)")


# ── Рассылка ──
async def start_broadcast(message: Message, state: FSMContext):
    await state.set_state(Broadcast.content)
    await state.update_data(text=None, photo=None)
    await message.answer(
        "📣 <b>Рассылка</b>\nПришлите текст сообщения — можно с фото и форматированием "
        "(жирный, курсив, ссылки). Дальше выберете, кому отправить, и я покажу предпросмотр.\n"
        "Получат только подписанные. Отмена — /cancel"
    )


@seller_router.message(Command("broadcast"))
async def s_broadcast(m: Message, state: FSMContext):
    await start_broadcast(m, state)


@seller_router.message(Broadcast.content, F.text | F.photo)
async def s_broadcast_content(m: Message, state: FSMContext):
    if m.text and m.text.startswith("/"):
        await m.answer("Пришлите текст рассылки обычным сообщением или нажмите /cancel.")
        return
    plain = m.text or m.caption or ""
    if not plain.strip() and not m.photo:
        return
    if len(plain) > (900 if m.photo else 3500):
        await m.answer(f"Слишком длинно ({len(plain)} симв.): с фото — до 900, без фото — до 3500.")
        return
    text = m.html_text if plain else ""
    photo = m.photo[-1].file_id if m.photo else None
    try:  # предпросмотр — заодно проверяет, что разметка корректна
        if photo:
            await m.answer_photo(photo, caption=text or None)
        else:
            await m.answer(text)
    except TelegramBadRequest as e:
        await m.answer(f"⚠️ Не получилось оформить сообщение: {html.escape(str(e))}")
        return
    await state.update_data(text=text, photo=photo)
    kb = InlineKeyboardBuilder()
    for kind, label in AUDIENCES.items():
        kb.button(text=f"{label} ({len(audience_ids(kind))})", callback_data=f"bc:aud:{kind}")
    kb.button(text="❌ Отмена", callback_data="bc:cancel")
    kb.adjust(1)
    await m.answer(
        "👆 Так увидят покупатели (под сообщением будет кнопка «Отписаться»).\n"
        "Кому отправить? Чтобы заменить текст, просто пришлите новый.",
        reply_markup=kb.as_markup(),
    )


@seller_router.callback_query(F.data.startswith("bc:aud:"))
async def s_bc_audience(cb: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    if data.get("text") is None:
        await cb.answer("Сначала пришлите текст — /broadcast", show_alert=True)
        return
    kind = cb.data.split(":")[2]
    if kind not in AUDIENCES:
        await cb.answer()
        return
    ids = audience_ids(kind)
    if not ids:
        await cb.answer("В этой аудитории никого нет", show_alert=True)
        return
    with db() as c:
        last = c.execute("SELECT created_at FROM broadcasts ORDER BY id DESC LIMIT 1").fetchone()
    warn = ""
    if last and datetime.now(ZoneInfo(TZ)) - datetime.strptime(last[0], "%Y-%m-%d %H:%M:%S").replace(
        tzinfo=ZoneInfo(TZ)
    ) < timedelta(hours=12):
        warn = "⚠️ Прошлая рассылка была меньше 12 часов назад — частые рассылки раздражают.\n\n"
    kb = InlineKeyboardBuilder()
    kb.button(text=f"✅ Отправить ({len(ids)})", callback_data=f"bc:go:{kind}")
    kb.button(text="❌ Отмена", callback_data="bc:cancel")
    kb.adjust(1)
    await cb.message.edit_text(
        f"Получатели: <b>{AUDIENCES[kind]}</b> — {len(ids)} чел.\n\n{warn}Отправляем?", reply_markup=kb.as_markup()
    )
    await cb.answer()


@seller_router.callback_query(F.data == "bc:cancel")
async def s_bc_cancel(cb: CallbackQuery, state: FSMContext):
    await state.clear()
    await cb.message.edit_text("Рассылка отменена.")
    await cb.answer()


@seller_router.callback_query(F.data.startswith("bc:go:"))
async def s_bc_go(cb: CallbackQuery, state: FSMContext):
    data = await state.get_data()
    kind = cb.data.split(":")[2]
    if data.get("text") is None or kind not in AUDIENCES:
        await cb.answer("Сначала пришлите текст — /broadcast", show_alert=True)
        return
    if bc_state["running"]:
        await cb.answer("Другая рассылка ещё идёт — дождитесь итога", show_alert=True)
        return
    ids = audience_ids(kind)
    if not ids:
        await cb.answer("В этой аудитории никого нет", show_alert=True)
        return
    photo_bytes = None
    if data.get("photo"):
        buf = await cb.bot.download(data["photo"])
        photo_bytes = buf.read()
    with db() as c:
        bid = c.execute(
            "INSERT INTO broadcasts(created_at, audience, text, total, has_photo) VALUES(?,?,?,?,?)",
            (now_str(), kind, data["text"], len(ids), int(bool(photo_bytes))),
        ).lastrowid
    await state.clear()
    bc_state["running"] = True
    task = asyncio.create_task(run_broadcast(bid, ids, data["text"], photo_bytes))
    bc_tasks.add(task)
    task.add_done_callback(bc_tasks.discard)
    await cb.message.edit_text(f"🚀 Рассылка #{bid} запущена: {len(ids)} получателей. Итог пришлю сюда.")
    await cb.answer()


# ── Все остальные в боте продавца ──
@guest_router.message()
async def g_message(m: Message):
    await m.answer(
        "Это бот продавца, доступ только по ID.\n"
        f"Ваш Telegram ID: <code>{m.from_user.id}</code>\n"
        f"ADMIN_ID в настройках: <code>{ADMIN_ID}</code>"
    )


@guest_router.callback_query()
async def g_callback(cb: CallbackQuery):
    await cb.answer("Нет доступа", show_alert=True)


# ───────────────────────── Меню команд (выпадающий список) ─────────────────────────
CUSTOMER_COMMANDS = [
    ("menu", "🛍 Каталог"),
    ("search", "🔎 Поиск товара"),
    ("friend", "🎁 Пригласить друга"),
    ("support", "🆘 Поддержка"),
    ("news", "🔔 Рассылка: вкл/выкл"),
    ("promo", "🏷 Ввести промокод"),
    ("myorders", "📦 Мои заказы"),
    ("hours", "🕐 Режим работы"),
    ("suggest", "💡 Предложить товар"),
    ("ideas", "🗳 Идеи покупателей"),
    ("myid", "🆔 Мой Telegram ID"),
    ("cancel", "✖️ Отменить ввод"),
]
SELLER_COMMANDS = [
    ("orders", "📋 Активные заказы"),
    ("receipt", "🧾 Чек по заказу"),
    ("stats", "📈 Статистика"),
    ("stock", "📦 Склад и остатки"),
    ("suggestions", "💡 Предложения покупателей"),
    ("setprice", "💰 Изменить цену"),
    ("setstock", "🔢 Изменить остаток"),
    ("setcost", "🧾 Закупочная цена"),
    ("setdesc", "📝 Описание товара"),
    ("setphoto", "🖼 Фото товара"),
    ("setsku", "🏷 Артикул товара"),
    ("setcat", "🗂 Категория товара"),
    ("rename", "✏️ Переименовать товар"),
    ("add", "➕ Добавить товар"),
    ("hide", "🙈 Скрыть товар"),
    ("show", "👀 Показать товар"),
    ("sale", "🔥 Акция на товар"),
    ("newpromo", "🎟 Создать промокод"),
    ("promos", "🎟 Список промокодов"),
    ("delpromo", "🗑 Удалить промокод"),
    ("template", "📥 Образец файла для загрузки"),
    ("import", "📥 Загрузить товары из файла"),
    ("export", "📤 Выгрузить товары в файл"),
    ("hours", "🕐 Режим работы"),
    ("pick", "🧺 Сборочный лист"),
    ("users", "👥 Пользователи бота"),
    ("broadcast", "📣 Рассылка покупателям"),
    ("tickets", "🆘 Обращения клиентов"),
    ("report", "🌅 Отчёт за ночь"),
    ("backup", "💾 Резервная копия"),
    ("restore", "♻️ Восстановить из копии"),
    ("soldout", "🙈 Закончившиеся товары"),
    ("closeshop", "🔴 Закрыть магазин"),
    ("openshop", "🟢 Открыть магазин"),
    ("help", "❓ Справка по командам"),
    ("cancel", "✖️ Отменить ввод"),
]


async def setup_seller_commands(bot):
    """Меню команд видно только продавцу. Если он ещё не нажимал /start — Telegram откажет,
    поэтому повторяем при его /start."""
    try:
        await bot.set_my_commands(
            [BotCommand(command=c, description=d) for c, d in SELLER_COMMANDS],
            scope=BotCommandScopeChat(chat_id=ADMIN_ID),
        )
        await bot.set_chat_menu_button(chat_id=ADMIN_ID, menu_button=MenuButtonCommands())
    except Exception:
        logging.warning("Меню команд продавца появится после его /start в боте продавца.")


async def setup_commands():
    try:
        await bots["customer"].set_my_commands(
            [BotCommand(command=c, description=d) for c, d in CUSTOMER_COMMANDS],
            scope=BotCommandScopeDefault(),
        )
        await bots["customer"].set_chat_menu_button(menu_button=MenuButtonCommands())
    except Exception:
        logging.exception("Не удалось задать меню команд покупателя")
    await setup_seller_commands(bots["seller"])


# ───────────────────────── Защита от спама ─────────────────────────
class ThrottleMiddleware(BaseMiddleware):
    """Не больше RATE_LIMIT событий от одного человека за RATE_WINDOW секунд.
    При превышении — пауза RATE_BLOCK секунд: бот просто не реагирует. Продавец не ограничивается."""

    def __init__(self):
        self.hits = {}
        self.blocked = {}

    async def __call__(self, handler, event, data):
        user = data.get("event_from_user")
        if user is None or user.id == ADMIN_ID or RATE_LIMIT <= 0:
            return await handler(event, data)
        now = time.monotonic()
        if now < self.blocked.get(user.id, 0):
            if isinstance(event, CallbackQuery):
                await event.answer()  # чтобы у кнопки не крутились «часики»
            return None
        q = self.hits.setdefault(user.id, deque())
        while q and now - q[0] > RATE_WINDOW:
            q.popleft()
        q.append(now)
        if len(q) > RATE_LIMIT:
            self.blocked[user.id] = now + RATE_BLOCK
            q.clear()
            text = f"⏳ Слишком много запросов подряд. Подождите {RATE_BLOCK} сек."
            if isinstance(event, CallbackQuery):
                await event.answer(text, show_alert=True)
            elif isinstance(event, Message):
                await event.answer(text)
            return None
        if len(self.hits) > 5000:  # чистим память от давно не писавших
            for uid in [u for u, d in self.hits.items() if not d or now - d[-1] > 3600]:
                self.hits.pop(uid, None)
                self.blocked.pop(uid, None)
        return await handler(event, data)


# ───────────────────────── Расписание: резервная копия и отчёт ─────────────────────────
async def run_scheduled():
    now = datetime.now(ZoneInfo(TZ))
    cur, today = now.hour * 60 + now.minute, now.strftime("%Y-%m-%d")

    bt = parse_hhmm(BACKUP_TIME)
    if bt is not None and cur >= bt and get_setting("last_backup") != today:
        set_setting("last_backup", today)  # сначала отметка — чтобы при сбое не слать каждую минуту
        try:
            await send_backup(bots["seller"])
        except Exception:
            logging.exception("Не удалось отправить резервную копию")

    rt = parse_hhmm(REPORT_TIME)
    if rt is not None and cur >= rt and get_setting("last_report") != today:
        set_setting("last_report", today)
        try:
            await bots["seller"].send_message(
                ADMIN_ID, "🌅 <b>Отчёт за ночь</b>\n\n" + stats_text("night"), reply_markup=stats_kb("night")
            )
        except Exception:
            logging.exception("Не удалось отправить отчёт")


async def scheduler():
    while True:
        try:
            await run_scheduled()
        except Exception:
            logging.exception("Ошибка расписания")
        await asyncio.sleep(60)


# ───────────────────────── Бронь: автоотмена неоплаченных заказов ─────────────────────────
async def reserve_watcher():
    while True:
        try:
            expired, warn = process_reservations()
            for o in warn:
                b = InlineKeyboardBuilder()
                b.button(text="💸 Я оплатил(а)", callback_data=f"paid:{o['id']}")
                await tell_customer(
                    o["user_id"],
                    f"⏳ Заказ #{o['id']} ждёт оплаты. Бронь закончится примерно через 5 минут — "
                    "переведите сумму и нажмите кнопку ниже.",
                    b.as_markup(),
                )
            for o in expired:
                await tell_customer(
                    o["user_id"],
                    f"⏰ Заказ #{o['id']} отменён: оплата не поступила за {RESERVE_MINUTES} мин. "
                    "Товар вернулся в продажу. Оформить заново: /menu",
                )
                await notify_seller(
                    f"⏰ Заказ #{o['id']} на {o['total']} ₽ отменён автоматически: "
                    f"не оплачен за {RESERVE_MINUTES} мин. Товар вернулся на склад."
                )
        except Exception:
            logging.exception("Ошибка проверки брони")
        await asyncio.sleep(60)


# ───────────────────────── Учёт пользователей ─────────────────────────
class UserTrackMiddleware(BaseMiddleware):
    """Запоминает каждого, кто пишет боту покупателя (и по ссылке-приглашению ref_<id> — кто пригласил)."""

    def __init__(self):
        self.seen = {}

    async def __call__(self, handler, event, data):
        user = data.get("event_from_user")
        if user is not None and not user.is_bot:
            ref_id = None
            if isinstance(event, Message) and (event.text or "").startswith("/start "):
                payload = event.text.split(maxsplit=1)[1].strip()
                if payload.startswith("ref_") and payload[4:].isdigit():
                    ref_id = int(payload[4:])
            now = time.monotonic()
            if ref_id or now - self.seen.get(user.id, -1e9) > 60:  # в БД пишем не чаще раза в минуту
                self.seen[user.id] = now
                try:
                    data["new_user"] = register_user(user, ref_id)
                except Exception:
                    logging.exception("Не удалось записать пользователя")
        return await handler(event, data)


# ───────────────────────── Рассылка (фоновая отправка) ─────────────────────────
bc_state = {"running": False}
bc_tasks = set()


async def run_broadcast(bid, ids, text, photo_bytes):
    bot = bots["customer"]
    kb = InlineKeyboardMarkup(
        inline_keyboard=[[InlineKeyboardButton(text="🔕 Отписаться от рассылки", callback_data="news:off")]]
    )
    sent = failed = blocked = 0
    cached_fid = None
    try:
        for uid in ids:
            ok = False
            for _ in range(2):  # вторая попытка — после паузы, если Telegram попросил подождать
                try:
                    if photo_bytes:
                        media = cached_fid or BufferedInputFile(photo_bytes, filename="promo.jpg")
                        msg = await bot.send_photo(uid, media, caption=text or None, reply_markup=kb)
                        cached_fid = msg.photo[-1].file_id
                    else:
                        await bot.send_message(uid, text, reply_markup=kb)
                    ok = True
                    break
                except TelegramRetryAfter as e:
                    await asyncio.sleep(e.retry_after + 1)
                except TelegramForbiddenError:
                    mark_blocked(uid)
                    blocked += 1
                    break
                except Exception:
                    logging.warning("Рассылка: не доставлено %s", uid)
                    break
            sent += ok
            failed += not ok
            await asyncio.sleep(0.06)  # ~16 сообщений в секунду — с запасом до лимита Telegram
    finally:
        bc_state["running"] = False
        with db() as c:
            c.execute("UPDATE broadcasts SET sent=?, failed=? WHERE id=?", (sent, failed, bid))
        await notify_seller(
            f"📣 <b>Рассылка #{bid} завершена</b>\nДоставлено: <b>{sent}</b> из {len(ids)}"
            + (f"\nНе доставлено: {failed}" + (f" (из них заблокировали бота: {blocked})" if blocked else "") if failed else "")
        )


# ───────────────────────── Уведомления «товар появился» ─────────────────────────
async def restock_watcher():
    while True:
        try:
            with db() as c:
                rows = c.execute(
                    """SELECT s.user_id, s.product_id, p.name, p.stock, p.price, p.sale_price
                       FROM stock_subs s JOIN products p ON p.id = s.product_id
                       WHERE p.active=1 AND p.stock>0"""
                ).fetchall()
            for r in rows:
                kb = InlineKeyboardBuilder()
                kb.button(text="🛒 Открыть товар", callback_data=f"p:{r['product_id']}:all")
                few = "\nОсталось немного — успейте!" if r["stock"] <= 3 else ""
                await tell_customer(
                    r["user_id"],
                    f"🔔 <b>{html.escape(r['name'])}</b> снова в наличии — "
                    f"{eff_price(r['sale_price'] or r['price'])} ₽, {r['stock']} шт.{few}",
                    kb.as_markup(),
                )
                with db() as c:  # подписка одноразовая: снимаем сразу после отправки (при сбое не потеряем остальных)
                    c.execute("DELETE FROM stock_subs WHERE user_id=? AND product_id=?", (r["user_id"], r["product_id"]))
                await asyncio.sleep(0.05)
        except Exception:
            logging.exception("Ошибка уведомлений о поступлении")
        await asyncio.sleep(20)


# ───────────────────────── Запуск ─────────────────────────
def acquire_single_instance_lock():
    """Не даём запустить второй экземпляр на этом компьютере."""
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        sock.bind(("127.0.0.1", 47653))
    except OSError:
        raise SystemExit(
            "❌ Бот уже запущен на этом компьютере (другое окно или процесс python). "
            "Закройте его и запустите снова."
        )
    return sock


async def main():
    logging.basicConfig(level=logging.INFO)
    if BOT_TOKEN == SELLER_BOT_TOKEN:
        raise SystemExit("❌ BOT_TOKEN и SELLER_BOT_TOKEN должны быть токенами РАЗНЫХ ботов.")
    lock = acquire_single_instance_lock()  # noqa: F841 (держим сокет открытым)
    os.makedirs(os.path.dirname(os.path.abspath(DB_PATH)), exist_ok=True)  # на хостинге: /app/data
    os.makedirs(PHOTOS_DIR, exist_ok=True)
    init_db()
    logging.info("База данных: %s", DB_PATH)

    props = DefaultBotProperties(parse_mode=ParseMode.HTML)
    bots["customer"] = Bot(BOT_TOKEN, default=props)
    bots["seller"] = Bot(SELLER_BOT_TOKEN, default=props)

    dp_customer = Dispatcher(storage=MemoryStorage())
    dp_customer.message.outer_middleware(ThrottleMiddleware())
    dp_customer.callback_query.outer_middleware(ThrottleMiddleware())
    track = UserTrackMiddleware()  # после антиспама: флуд в базу не пишем
    dp_customer.message.outer_middleware(track)
    dp_customer.callback_query.outer_middleware(track)
    dp_customer.include_router(customer_router)
    dp_seller = Dispatcher(storage=MemoryStorage())
    dp_seller.message.outer_middleware(ThrottleMiddleware())  # посторонних в боте продавца тоже ограничиваем
    dp_seller.callback_query.outer_middleware(ThrottleMiddleware())
    dp_seller.include_router(seller_router)
    dp_seller.include_router(guest_router)

    try:
        bots["customer_username"] = (await bots["customer"].get_me()).username  # для ссылок-приглашений
    except Exception:
        logging.exception("Не удалось узнать имя бота покупателя")
    await setup_commands()
    await asyncio.gather(
        dp_customer.start_polling(bots["customer"], handle_signals=False),
        dp_seller.start_polling(bots["seller"], handle_signals=False),
        reserve_watcher(),
        restock_watcher(),
        scheduler(),
    )


if __name__ == "__main__":
    asyncio.run(main())