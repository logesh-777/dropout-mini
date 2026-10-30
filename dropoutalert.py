"""DropoutAlert - Student Dropout Early Warning System (single-file edition)

One Python file containing the database models, API, risk engine, login and permissions,
and the complete web app. Open the site at "/".  The API lives under "/api".

Scores are ILLUSTRATIVE indicators that point staff to students who may need support.
They are not validated predictions of dropout, and nothing here acts on a student automatically.

WHO CAN DO WHAT
    admin    everything: accounts, risk rules, student help text, audit trail, CSV import
    faculty  only the students in their assigned courses: records, attendance, interventions
    support  every student's progress and interventions; cannot edit marks or attendance
    student  sees only their OWN attendance, marks, assignments, support plan and help text.
             No risk score or category and no staff notes. Admins create student accounts
             (Settings > Create an account, linked by student code such as S1001).
    Also: PDF reports (summary, per student, and a student's own), saved directory filters,
    bulk interventions, alert preferences, weekly attendance history, follow-up calendar.

QUICK START (your computer)
    pip install flask flask-sqlalchemy
    export SECRET_KEY="$(python -c 'import secrets;print(secrets.token_hex(32))')"
    export ADMIN_EMAIL=you@college.edu ADMIN_NAME="Your Name" ADMIN_PASSWORD='Choose-a-Strong-1'
    export SEED_DEMO=1            # optional: fictional demo users and students (password demo1234)
    python dropoutalert.py        # open http://127.0.0.1:5000

DEPLOY (Render, Railway, a VPS, ...)
    Install command : pip install flask flask-sqlalchemy gunicorn psycopg2-binary
    Start command   : gunicorn -w 2 -b 0.0.0.0:$PORT dropoutalert:app
    Environment variables:
      APP_ENV=production            requires SECRET_KEY and PUBLIC_URL, makes cookies Secure
      SECRET_KEY=<long random>      keep it secret and the same on every worker
      PUBLIC_URL=https://your-site  used in password reset emails
      DATABASE_URL=postgresql://... use PostgreSQL in production. SQLite files are erased on
                                    hosts with an ephemeral disk. "postgres://" is accepted too.
      TRUST_PROXY=1                 when a proxy/load balancer terminates HTTPS in front of the app
      ADMIN_EMAIL / ADMIN_NAME / ADMIN_PASSWORD   creates the first administrator once, if none exists
      SMTP_HOST SMTP_PORT SMTP_USER SMTP_PASSWORD MAIL_FROM   real password-reset email
      LOGIN_IMAGE_URL=https://...   optional https photo for the sign-in page (a licensed campus photo)
      SESSION_HOURS=8               SEED_DEMO=1 (+ DEMO_PASSWORD in production) for demo data
    Health check: GET /healthz

HONEST NOTES
    - Without SMTP_HOST, password-reset links are only logged, never emailed, and the app never says it sent one.
    - Tables are created automatically on start. For later schema changes use a migration tool (Alembic).
    - Back up the database on a schedule (pg_dump for PostgreSQL) and test restoring it.
    - Run "flask --app dropoutalert run-rules" from cron if you want overdue alerts without anyone opening the app
      (they are also created whenever someone loads their alerts).
    - PDF reports use standard fonts, so characters outside Western European alphabets print as '?'.
    - Interface text and layout were checked with scripted tests, not by eye in many real browsers.
"""
import csv
import hashlib
import io
import logging
import os
import re
import secrets
import smtplib
import time
import types
from copy import deepcopy
from datetime import date, datetime, timedelta, timezone
from email.message import EmailMessage
from functools import wraps

import click
from flask import Blueprint, Flask, Response, current_app, g, jsonify, request, session
from flask_sqlalchemy import SQLAlchemy
from sqlalchemy import func, or_
from sqlalchemy.exc import IntegrityError, OperationalError, ProgrammingError
from werkzeug.exceptions import HTTPException
from werkzeug.middleware.proxy_fix import ProxyFix
from werkzeug.security import check_password_hash, generate_password_hash


# =============================================================================
# Risk engine
# =============================================================================
"""Transparent, configurable risk scoring.

These are illustrative demonstration rules, not a validated dropout prediction model.
A score points staff to students who may benefit from a human conversation.
"""

DEFAULT_RULES = {
    "attendance": [[60, 40], [75, 25]],   # [[below, points], [below, points]]
    "marks": [[40, 35], [55, 20]],
    "assignments": [[50, 25], [75, 10]],
    "medium": 30,
    "high": 60,
    "stale_days": 30,
}
FACTORS = (("attendance", "Attendance"), ("marks", "Marks"), ("assignments", "Assignment completion"))
RANK = {"low": 0, "incomplete": 0, "medium": 1, "high": 2}


def default_rules():
    return deepcopy(DEFAULT_RULES)


def _num(v):
    return isinstance(v, (int, float)) and not isinstance(v, bool)


def validate_rules(data):
    """Return (clean_rules, errors)."""
    errors, clean = {}, default_rules()
    for key, _ in FACTORS:
        bands = data.get(key, clean[key])
        ok = (isinstance(bands, list) and len(bands) == 2 and all(isinstance(b, list) and len(b) == 2 and all(_num(x) and 0 <= x <= 100 for x in b) for b in bands))
        if not ok:
            errors[key] = "must be two [threshold, points] pairs with numbers from 0 to 100"
        elif bands[0][0] >= bands[1][0]:
            errors[key] = "the first threshold must be below the second"
        else:
            clean[key] = [[float(b[0]), float(b[1])] for b in bands]
    med, high = data.get("medium", clean["medium"]), data.get("high", clean["high"])
    if not (_num(med) and _num(high) and 0 <= med < high <= 100):
        errors["medium"] = "medium must be below high, both from 0 to 100"
    else:
        clean["medium"], clean["high"] = float(med), float(high)
    stale = data.get("stale_days", clean["stale_days"])
    if not (_num(stale) and 1 <= stale <= 3650):
        errors["stale_days"] = "must be between 1 and 3650"
    else:
        clean["stale_days"] = int(stale)
    return clean, errors


def band_points(value, bands):
    if value < bands[0][0]:
        return bands[0][1]
    if value < bands[1][0]:
        return bands[1][1]
    return 0


def category_for(score, rules):
    return "high" if score >= rules["high"] else "medium" if score >= rules["medium"] else "low"


def assess(values, rules):
    """values: dict with attendance/marks/assignments, any of which may be None (missing).

    Missing data is never treated as good performance: if nothing else raises the
    category, the result is 'incomplete' rather than 'low'.
    """
    total, factors, missing = 0, [], []
    for key, label in FACTORS:
        v = values.get(key)
        if v is None:
            missing.append(label)
            factors.append({"factor": label, "value": None, "points": None})
        else:
            p = band_points(v, rules[key])
            total += p
            factors.append({"factor": label, "value": v, "points": p})
    total = min(100, total)
    cat = category_for(total, rules)
    if missing and cat == "low":
        cat = "incomplete"
    return {"score": total, "category": cat, "factors": factors, "missing": missing}


def is_stale(updated_at, rules, now=None):
    if updated_at is None:
        return True
    now = now or datetime.now(timezone.utc).replace(tzinfo=None)
    return now - updated_at > timedelta(days=rules["stale_days"])

risk = types.SimpleNamespace(default_rules=default_rules, validate_rules=validate_rules, band_points=band_points, category_for=category_for,
                             assess=assess, is_stale=is_stale, RANK=RANK, FACTORS=FACTORS, DEFAULT_RULES=DEFAULT_RULES)


# =============================================================================
# Errors and database models
# =============================================================================
log = logging.getLogger(__name__)


class ApiError(Exception):
    def __init__(self, code, message, status=400, details=None):
        super().__init__(message)
        self.code, self.message, self.status, self.details = code, message, status, details or {}


def respond(code, message, status, details=None):
    return jsonify({"error": {"code": code, "message": message, "details": details or {}}}), status


def register_errors(app):
    @app.errorhandler(ApiError)
    def _api(e):
        return respond(e.code, e.message, e.status, e.details)

    @app.errorhandler(HTTPException)
    def _http(e):
        return respond(e.name.lower().replace(" ", "_"), e.description, e.code)

    @app.errorhandler(Exception)
    def _unexpected(e):
        log.exception("Unhandled error")  # details stay in the server log, never in the response
        return respond("server_error", "Something went wrong on the server.", 500)


db = SQLAlchemy()


def utcnow():
    return datetime.now(timezone.utc).replace(tzinfo=None)


class User(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    email = db.Column(db.String(254), unique=True, nullable=False, index=True)
    name = db.Column(db.String(120), nullable=False)
    password_hash = db.Column(db.String(255), nullable=False)
    role = db.Column(db.String(20), nullable=False)  # admin | faculty | support
    courses = db.Column(db.JSON, nullable=False, default=list)  # faculty course scope
    prefs = db.Column(db.JSON, nullable=False, default=lambda: {"risk": True, "overdue": True, "assign": True})
    student_id = db.Column(db.Integer, db.ForeignKey("student.id"), unique=True)  # set for student accounts
    active = db.Column(db.Boolean, nullable=False, default=False)
    session_version = db.Column(db.Integer, nullable=False, default=1)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    __table_args__ = (db.CheckConstraint("role IN ('admin','faculty','support','student')", name="ck_user_role"),)

    def set_password(self, pw):
        self.password_hash = generate_password_hash(pw)
        self.session_version = (self.session_version or 1) + 1  # signs out other sessions

    def check_password(self, pw):
        return check_password_hash(self.password_hash, pw)

    def to_json(self):  # never includes the password hash
        return {"id": self.id, "email": self.email, "name": self.name, "role": self.role, "courses": self.courses or [], "active": self.active, "student_id": self.student_id}


class Student(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    code = db.Column(db.String(30), unique=True, nullable=False)
    name = db.Column(db.String(120), nullable=False)
    course = db.Column(db.String(80), nullable=False, index=True)
    attendance = db.Column(db.Float)
    marks = db.Column(db.Float)
    assignments = db.Column(db.Float)
    data_updated_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    risk_score = db.Column(db.Float)
    risk_category = db.Column(db.String(12), index=True)
    risk_missing = db.Column(db.JSON, default=list)
    risk_factors = db.Column(db.JSON, default=list)
    assessed_at = db.Column(db.DateTime)
    __table_args__ = (
        db.UniqueConstraint("name", "course", name="uq_student_name_course"),
        db.CheckConstraint("attendance IS NULL OR (attendance >= 0 AND attendance <= 100)", name="ck_att"),
        db.CheckConstraint("marks IS NULL OR (marks >= 0 AND marks <= 100)", name="ck_marks"),
        db.CheckConstraint("assignments IS NULL OR (assignments >= 0 AND assignments <= 100)", name="ck_asg"),
    )


class Assessment(db.Model):
    """History of every recalculation."""
    id = db.Column(db.Integer, primary_key=True)
    student_id = db.Column(db.Integer, db.ForeignKey("student.id"), nullable=False, index=True)
    score = db.Column(db.Float, nullable=False)
    category = db.Column(db.String(12), nullable=False)
    factors = db.Column(db.JSON, nullable=False)
    reason = db.Column(db.String(40), nullable=False)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)


class AttendanceRecord(db.Model):
    """One attendance percentage per student per week (Monday start)."""
    id = db.Column(db.Integer, primary_key=True)
    student_id = db.Column(db.Integer, db.ForeignKey("student.id"), nullable=False, index=True)
    week_start = db.Column(db.Date, nullable=False)
    percent = db.Column(db.Float, nullable=False)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    __table_args__ = (db.UniqueConstraint("student_id", "week_start", name="uq_att_student_week"),
                      db.CheckConstraint("percent >= 0 AND percent <= 100", name="ck_att_percent"))


class Intervention(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    student_id = db.Column(db.Integer, db.ForeignKey("student.id"), nullable=False, index=True)
    category = db.Column(db.String(30), nullable=False)
    priority = db.Column(db.String(10), nullable=False)
    assignee_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False)
    created_by = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False)
    description = db.Column(db.Text, nullable=False)
    due_date = db.Column(db.Date, nullable=False)
    status = db.Column(db.String(15), nullable=False, default="planned", index=True)
    outcome = db.Column(db.String(15))
    notes = db.Column(db.Text)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    completed_at = db.Column(db.DateTime)
    __table_args__ = (
        db.CheckConstraint("status IN ('planned','in_progress','completed','cancelled')", name="ck_iv_status"),
        db.CheckConstraint("priority IN ('low','medium','high')", name="ck_iv_priority"),
    )


class Notification(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False, index=True)
    key = db.Column(db.String(80), nullable=False)  # de-duplication key
    title = db.Column(db.String(200), nullable=False)
    body = db.Column(db.String(400), nullable=False)
    student_id = db.Column(db.Integer, db.ForeignKey("student.id"))
    read = db.Column(db.Boolean, nullable=False, default=False)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    __table_args__ = (db.UniqueConstraint("user_id", "key", name="uq_notification_key"),)


class Audit(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    actor_id = db.Column(db.Integer, db.ForeignKey("user.id"))
    action = db.Column(db.String(60), nullable=False)
    detail = db.Column(db.String(400), nullable=False, default="")
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)


class Setting(db.Model):
    key = db.Column(db.String(40), primary_key=True)
    value = db.Column(db.JSON, nullable=False)


class ResetToken(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False, index=True)
    token_hash = db.Column(db.String(64), unique=True, nullable=False)  # only a hash is stored
    expires_at = db.Column(db.DateTime, nullable=False)
    used = db.Column(db.Boolean, nullable=False, default=False)


class SavedView(db.Model):
    """A named set of student-directory filters that belongs to one user."""
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False, index=True)
    name = db.Column(db.String(60), nullable=False)
    params = db.Column(db.JSON, nullable=False)
    created_at = db.Column(db.DateTime, nullable=False, default=utcnow)
    __table_args__ = (db.UniqueConstraint("user_id", "name", name="uq_view_user_name"),)


class LoginFailure(db.Model):
    """Failed sign-ins, stored in the database so the limit holds across several workers."""
    id = db.Column(db.Integer, primary_key=True)
    email = db.Column(db.String(254), nullable=False, index=True)
    at = db.Column(db.DateTime, nullable=False, default=utcnow)


# =============================================================================
# Services
# =============================================================================
log = logging.getLogger(__name__)
BAD = re.compile(r'[<>&"\x00-\x1f]')
EMAIL = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


# ---- validation -------------------------------------------------------------
def text(d, key, lo, hi, errs, required=True):
    v = d.get(key)
    if v is None or v == "":
        if required:
            errs[key] = "is required"
        return None
    if not isinstance(v, str) or not lo <= len(v.strip()) <= hi or BAD.search(v):
        errs[key] = f"must be {lo} to {hi} characters without < > & or quotes"
        return None
    return v.strip()


def pct(d, key, errs):
    """Optional 0-100 number. None means 'missing', which is never treated as low risk."""
    v = d.get(key)
    if v is None or v == "":
        return None
    if isinstance(v, bool) or not isinstance(v, (int, float)) or not 0 <= v <= 100:
        errs[key] = "must be a number from 0 to 100"
        return None
    return float(v)


def check(errs):
    if errs:
        raise ApiError("validation", "Some fields are invalid.", 422, errs)


def check_password_strength(pw, email=""):
    if not isinstance(pw, str) or len(pw) < 8 or not re.search(r"[A-Za-z]", pw) or not re.search(r"\d", pw) or pw.lower() == email.lower():
        raise ApiError("validation", "Password must have at least 8 characters, including a letter and a number.", 422, {"password": "too weak"})


# ---- access -----------------------------------------------------------------
def current_user():
    uid = session.get("uid")
    u = db.session.get(User, uid) if uid else None
    if u and u.active and session.get("sv") == u.session_version:
        return u
    return None


def scoped(u):
    q = Student.query
    if u.role == "faculty":
        q = q.filter(Student.course.in_(u.courses or []))
    return q


def get_student(sid, u):
    s = scoped(u).filter(Student.id == sid).first()
    if not s:
        raise ApiError("not_found", "Student not found.", 404)  # same answer whether it exists or is out of scope
    return s


def audit(actor, action, detail=""):
    db.session.add(Audit(actor_id=actor.id if actor else None, action=action, detail=detail[:400]))


# ---- rules + scoring --------------------------------------------------------
def get_rules():
    row = db.session.get(Setting, "rules")
    merged = risk.default_rules()
    if row:
        merged.update(row.value)
    return merged


def recipients(student):
    out = []
    for u in User.query.filter_by(active=True):
        if u.role in ("admin", "support") or (u.role == "faculty" and student.course in (u.courses or [])):
            out.append(u)
    return out


PREF_OF = {"rise": "risk", "high": "risk", "stale": "risk", "overdue": "overdue", "assigned": "assign", "completed": "assign"}


def notify(users, key, title, body, student_id=None):
    n = 0
    for u in users:
        cat = PREF_OF.get(key.split(":")[0])
        if cat and (u.prefs or {}).get(cat) is False:
            continue  # the person turned this kind of alert off
        if Notification.query.filter_by(user_id=u.id, key=key).first():
            continue  # de-duplication: the same event never notifies twice
        db.session.add(Notification(user_id=u.id, key=key, title=title[:200], body=body[:400], student_id=student_id))
        n += 1
    return n


def recompute(s, reason, rules=None):
    rules = rules or get_rules()
    res = risk.assess({"attendance": s.attendance, "marks": s.marks, "assignments": s.assignments}, rules)
    prev = s.risk_category
    changed = prev is None or (res["score"], res["category"], res["missing"]) != (s.risk_score, s.risk_category, s.risk_missing or [])
    if changed:
        s.risk_score, s.risk_category, s.risk_missing, s.risk_factors, s.assessed_at = res["score"], res["category"], res["missing"], res["factors"], utcnow()
        a = Assessment(student_id=s.id, score=res["score"], category=res["category"], factors=res["factors"], reason=reason)
        db.session.add(a)
        db.session.flush()
        if prev is not None and risk.RANK[res["category"]] > risk.RANK[prev] and res["category"] in ("medium", "high"):
            notify(recipients(s), f"rise:{s.id}:{res['category']}:{a.id}", f"{s.name} moved to {res['category']} risk", f"Score is now {res['score']:g}. Please review.", s.id)
    return changed


def run_overdue_rule(today=None):
    """Defined backend rule: notify the assignee once when a follow-up date has passed."""
    today = today or date.today()
    made = 0
    for iv in Intervention.query.filter(Intervention.status.in_(("planned", "in_progress")), Intervention.due_date < today):
        assignee = db.session.get(User, iv.assignee_id)
        st = db.session.get(Student, iv.student_id)
        if assignee and assignee.active:
            made += notify([assignee], f"overdue:{iv.id}", f"Follow-up overdue: {st.name}", f"{iv.category} support was due {iv.due_date.isoformat()}.", st.id)
    db.session.commit()
    return made


# ---- attendance history -----------------------------------------------------
def week_of(d):
    return d - timedelta(days=d.weekday())  # Monday


def upsert_week(s, percent, week=None):
    week = week_of(week or date.today())
    rec = AttendanceRecord.query.filter_by(student_id=s.id, week_start=week).first()
    if rec:
        rec.percent = percent
    else:
        rec = AttendanceRecord(student_id=s.id, week_start=week, percent=percent)
        db.session.add(rec)
    db.session.flush()
    return rec


# ---- email ------------------------------------------------------------------
def send_mail(to, subject, body):
    """Sends through SMTP when SMTP_HOST is set. Otherwise it is only logged and kept in
    app.outbox for development. It never pretends an email was delivered."""
    host = os.environ.get("SMTP_HOST")
    if not host:
        current_app.outbox.append({"to": to, "subject": subject, "body": body})
        log.info("DEV MAIL (not sent) to %s: %s", to, subject)
        return False
    msg = EmailMessage()
    msg["From"], msg["To"], msg["Subject"] = os.environ.get("MAIL_FROM", "noreply@dropoutalert.local"), to, subject
    msg.set_content(body)
    with smtplib.SMTP(host, int(os.environ.get("SMTP_PORT", "587"))) as smtp:
        smtp.starttls()
        if os.environ.get("SMTP_USER"):
            smtp.login(os.environ["SMTP_USER"], os.environ.get("SMTP_PASSWORD", ""))
        smtp.send_message(msg)
    return True


# ---- csv --------------------------------------------------------------------
def csv_cell(v):
    s = "" if v is None else str(v)
    return "'" + s if s[:1] in ("=", "+", "-", "@") else s  # blocks spreadsheet formula injection


def parse_import(text_data, existing):
    reader = csv.DictReader(io.StringIO(text_data))
    heads = [(h or "").strip().lower() for h in (reader.fieldnames or [])]
    need = ["name", "course", "attendance", "marks", "assignments"]
    miss = [n for n in need if n not in heads]
    if miss:
        raise ApiError("validation", "Missing column(s): " + ", ".join(miss), 422)
    seen, rows = set(existing), []
    for i, raw in enumerate(reader, start=2):
        if i > 501:
            raise ApiError("validation", "Please import at most 500 rows at a time.", 422)
        r = {(k or "").strip().lower(): (v or "").strip() for k, v in raw.items()}
        errs = {}
        nums = {}
        for k in ("attendance", "marks", "assignments"):
            try:
                nums[k] = pct({k: float(r[k]) if r[k] != "" else None}, k, errs)
            except ValueError:
                errs[k] = "must be a number from 0 to 100"
        name, course = text(r, "name", 2, 120, errs), text(r, "course", 1, 80, errs)
        if name and course:
            key = (name.lower(), course.lower())
            if key in seen:
                errs["name"] = "duplicate student in this course"
            else:
                seen.add(key)
        rows.append({"line": i, "ok": not errs, "errors": errs, "data": {"name": name, "course": course, **nums}})
    return rows


# =============================================================================
# HTTP API
# =============================================================================
api = Blueprint("api", __name__, url_prefix="/api")
ALL_ROLES = ("admin", "faculty", "support", "student")
IV_TRANSITIONS = {"planned": {"in_progress", "cancelled"}, "in_progress": {"completed", "cancelled"}}


@api.before_request
def csrf_guard():
    # Cookie sessions plus a custom header the browser will not add cross-site by itself.
    if request.method in ("POST", "PUT", "PATCH", "DELETE") and request.headers.get("X-Requested-With") != "DropoutAlert":
        raise ApiError("csrf", "Missing X-Requested-With header.", 403)


def body():
    d = request.get_json(silent=True)
    return d if isinstance(d, dict) else {}


def require(*roles):
    def deco(f):
        @wraps(f)
        def wrapper(*a, **k):
            u = current_user()
            if not u:
                raise ApiError("unauthenticated", "Please sign in.", 401)
            if (roles and u.role not in roles) or (not roles and u.role == "student"):  # students use /me/* only
                raise ApiError("forbidden", "Your role cannot do this.", 403)
            g.user = u
            return f(*a, **k)
        return wrapper
    return deco


def iso(d):
    return d.isoformat() if d else None


def student_json(s, rules):
    return {"id": s.id, "code": s.code, "name": s.name, "course": s.course, "attendance": s.attendance, "marks": s.marks,
            "assignments": s.assignments, "data_updated_at": iso(s.data_updated_at), "outdated": risk.is_stale(s.data_updated_at, rules),
            "risk": {"score": s.risk_score, "category": s.risk_category, "missing": s.risk_missing or [], "factors": s.risk_factors or [], "assessed_at": iso(s.assessed_at)}}


def iv_json(i):
    a, st = db.session.get(User, i.assignee_id), db.session.get(Student, i.student_id)
    return {"id": i.id, "student_id": i.student_id, "student_name": st.name if st else "", "assignee_name": a.name if a else "", "category": i.category, "priority": i.priority, "assignee_id": i.assignee_id, "description": i.description,
            "due_date": iso(i.due_date), "status": i.status, "outcome": i.outcome, "notes": i.notes, "created_at": iso(i.created_at), "completed_at": iso(i.completed_at)}


@api.get("/health")
def health():
    return jsonify({"status": "ok"})


# ---- authentication ---------------------------------------------------------
@api.post("/auth/register")
def register():
    d, errs = body(), {}
    name, email = text(d, "name", 2, 120, errs), (d.get("email") or "").strip().lower()
    if not EMAIL.match(email) or len(email) > 254:
        errs["email"] = "must be a valid email address"
    role = d.get("role")
    if role not in ("faculty", "support"):
        errs["role"] = "public registration is only for faculty or student support"  # never admin
    check(errs)
    check_password_strength(d.get("password"), email)
    if User.query.filter_by(email=email).first():
        raise ApiError("conflict", "An account with this email already exists.", 409)
    u = User(email=email, name=name, role=role, courses=[], active=False)  # an administrator must approve it
    u.set_password(d["password"])
    db.session.add(u)
    audit(None, "user.registered", f"{email} as {role}")
    db.session.commit()
    return jsonify({"message": "Account created. An administrator must approve it before you can sign in."}), 201


@api.post("/auth/login")
def login():
    d = body()
    email = (d.get("email") or "").strip().lower()
    LoginFailure.query.filter(LoginFailure.at < utcnow() - timedelta(minutes=5)).delete()
    if LoginFailure.query.filter_by(email=email).count() >= 5:
        raise ApiError("rate_limited", "Too many attempts. Try again in a few minutes.", 429)
    u = User.query.filter_by(email=email).first()
    if not u or not u.active or not isinstance(d.get("password"), str) or not u.check_password(d["password"]):
        db.session.add(LoginFailure(email=email))
        db.session.commit()
        raise ApiError("invalid_credentials", "Invalid email or password, or the account is not active.", 401)
    LoginFailure.query.filter_by(email=email).delete()
    session.clear()  # prevents session fixation
    session.permanent = True
    session["uid"], session["sv"] = u.id, u.session_version
    audit(u, "auth.login")
    db.session.commit()
    return jsonify({"user": u.to_json()})


@api.post("/auth/logout")
def logout():
    session.clear()
    return jsonify({"message": "Signed out."})


@api.get("/auth/me")
@require(*ALL_ROLES)
def me():
    return jsonify({"user": g.user.to_json()})


@api.post("/auth/password")
@require(*ALL_ROLES)
def change_password():
    d = body()
    if not isinstance(d.get("current"), str) or not g.user.check_password(d["current"]):
        raise ApiError("invalid_credentials", "Your current password is not correct.", 401)
    check_password_strength(d.get("new"), g.user.email)
    g.user.set_password(d["new"])
    session["sv"] = g.user.session_version  # this session stays signed in, others end
    audit(g.user, "auth.password_changed")
    db.session.commit()
    return jsonify({"message": "Password updated."})


@api.post("/auth/forgot")
def forgot():
    email = (body().get("email") or "").strip().lower()
    u = User.query.filter_by(email=email).first() if EMAIL.match(email) else None
    if u and u.active:
        raw = secrets.token_urlsafe(32)
        db.session.add(ResetToken(user_id=u.id, token_hash=hashlib.sha256(raw.encode()).hexdigest(), expires_at=utcnow() + timedelta(minutes=30)))
        db.session.commit()
        base = (current_app.config.get("PUBLIC_URL") or request.host_url).rstrip("/") + "/"
        send_mail(u.email, "Reset your DropoutAlert password", f"Use this link within 30 minutes: {base}?token={raw}")
    return jsonify({"message": "If that address is registered, a reset link has been sent."}), 202  # same answer either way


@api.post("/auth/reset")
def reset():
    d = body()
    tok = ResetToken.query.filter_by(token_hash=hashlib.sha256(str(d.get("token", "")).encode()).hexdigest()).first()
    if not tok or tok.used or tok.expires_at < utcnow():
        raise ApiError("invalid_token", "This reset link is invalid or has expired.", 400)
    u = db.session.get(User, tok.user_id)
    check_password_strength(d.get("password"), u.email)
    u.set_password(d["password"])
    tok.used = True
    ResetToken.query.filter_by(user_id=u.id, used=False).update({"used": True})  # single use, and old links die too
    audit(u, "auth.password_reset")
    db.session.commit()
    return jsonify({"message": "Password updated. You can sign in now."})


# ---- users (administrator) --------------------------------------------------
@api.get("/users")
@require("admin")
def users_list():
    users = User.query.order_by(User.id).all()
    ids = [u.student_id for u in users if u.student_id]
    codes = {s.id: s.code for s in Student.query.filter(Student.id.in_(ids))} if ids else {}
    return jsonify({"users": [{**u.to_json(), "student_code": codes.get(u.student_id)} for u in users]})


@api.post("/users")
@require("admin")
def users_create():
    d, errs = body(), {}
    name, email = text(d, "name", 2, 120, errs), (d.get("email") or "").strip().lower()
    if not EMAIL.match(email):
        errs["email"] = "must be a valid email address"
    role = d.get("role")
    if role not in ("admin", "faculty", "support", "student"):
        errs["role"] = "must be admin, faculty, support or student"
    courses = d.get("courses", [])
    if not isinstance(courses, list) or not all(isinstance(c, str) and 1 <= len(c) <= 80 for c in courses):
        errs["courses"] = "must be a list of course names"
    student = None
    if role == "student":
        student = Student.query.filter_by(code=str(d.get("student_code") or "").strip()).first()
        if not student:
            errs["student_code"] = "no student has this code"
        elif User.query.filter_by(student_id=student.id).first():
            errs["student_code"] = "this student already has an account"
    check(errs)
    check_password_strength(d.get("password"), email)
    if User.query.filter_by(email=email).first():
        raise ApiError("conflict", "An account with this email already exists.", 409)
    u = User(email=email, name=name, role=role, courses=courses if role == "faculty" else [], active=True, student_id=student.id if student else None)
    u.set_password(d["password"])
    db.session.add(u)
    audit(g.user, "user.created", f"{email} as {role}")
    db.session.commit()
    return jsonify({"user": u.to_json()}), 201


@api.patch("/users/<int:uid>")
@require("admin")
def users_update(uid):
    u, d = db.session.get(User, uid), body()
    if not u:
        raise ApiError("not_found", "User not found.", 404)
    if u.id == g.user.id and (d.get("active") is False or ("role" in d and d["role"] != "admin")):
        raise ApiError("conflict", "You cannot lock yourself out.", 409)
    changes = []
    if "active" in d:
        if not isinstance(d["active"], bool):
            raise ApiError("validation", "active must be true or false.", 422)
        u.active = d["active"]
        if not u.active:
            u.session_version += 1  # ends their sessions
        changes.append(f"active={u.active}")
    if "role" in d:
        if d["role"] not in ("admin", "faculty", "support") or u.role == "student":
            raise ApiError("validation", "Roles can be changed between admin, faculty and support only.", 422)
        u.role = d["role"]
        u.session_version += 1
        changes.append(f"role={u.role}")
    if "courses" in d:
        if not isinstance(d["courses"], list) or not all(isinstance(c, str) for c in d["courses"]):
            raise ApiError("validation", "courses must be a list.", 422)
        u.courses = d["courses"]
        changes.append("courses")
    audit(g.user, "user.updated", f"{u.email}: {', '.join(changes)}")
    db.session.commit()
    return jsonify({"user": u.to_json()})


# ---- students ---------------------------------------------------------------
SORTS = {"name": Student.name, "course": Student.course, "risk_score": Student.risk_score, "attendance": Student.attendance,
         "marks": Student.marks, "assignments": Student.assignments, "created_at": Student.created_at}


@api.get("/students")
@require()
def students_list():
    a, rules = request.args, get_rules()
    q = scoped(g.user)
    if a.get("q"):
        q = q.filter(or_(Student.name.icontains(a["q"], autoescape=True), Student.code.icontains(a["q"], autoescape=True)))
    if a.get("course"):
        q = q.filter(Student.course == a["course"])
    if a.get("category"):
        q = q.filter(Student.risk_category == a["category"])
    col = SORTS.get(a.get("sort", "name"))
    if col is None:
        raise ApiError("validation", "Unknown sort field.", 422)
    q = q.order_by(col.desc() if a.get("order") == "desc" else col.asc(), Student.id)
    try:
        page, per = max(1, int(a.get("page", 1))), min(100, max(1, int(a.get("per_page", 20))))
    except ValueError:
        raise ApiError("validation", "page and per_page must be numbers.", 422)
    p = q.paginate(page=page, per_page=per, error_out=False)
    return jsonify({"students": [student_json(s, rules) for s in p.items], "page": p.page, "pages": p.pages, "total": p.total})


def apply_numbers(s, d, errs):
    for k in ("attendance", "marks", "assignments"):
        if k in d:
            setattr(s, k, pct(d, k, errs))


@api.post("/students")
@require("admin", "faculty")
def students_create():
    d, errs = body(), {}
    name, course = text(d, "name", 2, 120, errs), text(d, "course", 1, 80, errs)
    s = Student(name=name or "", course=course or "", code="pending-" + secrets.token_hex(6))
    apply_numbers(s, d, errs)
    check(errs)
    if g.user.role == "faculty" and course not in (g.user.courses or []):
        raise ApiError("forbidden", "That course is not assigned to you.", 403)
    db.session.add(s)
    try:
        db.session.flush()
    except IntegrityError:
        db.session.rollback()
        raise ApiError("conflict", "A student with this name already exists in that course.", 409)
    s.code = f"S{1000 + s.id}"
    if s.attendance is not None:
        upsert_week(s, s.attendance)
    recompute(s, "created")
    audit(g.user, "student.created", s.code)
    db.session.commit()
    return jsonify({"student": student_json(s, get_rules())}), 201


@api.get("/students/<int:sid>")
@require()
def students_get(sid):
    return jsonify({"student": student_json(get_student(sid, g.user), get_rules())})


@api.patch("/students/<int:sid>")
@require("admin", "faculty")
def students_update(sid):
    s, d, errs = get_student(sid, g.user), body(), {}
    if ("name" in d or "course" in d) and g.user.role != "admin":
        raise ApiError("forbidden", "Only administrators can rename a student or change the course.", 403)
    if "name" in d:
        s.name = text(d, "name", 2, 120, errs) or s.name
    if "course" in d:
        s.course = text(d, "course", 1, 80, errs) or s.course
    numeric = any(k in d for k in ("attendance", "marks", "assignments"))
    apply_numbers(s, d, errs)
    check(errs)
    if numeric:
        s.data_updated_at = utcnow()
        if "attendance" in d and s.attendance is not None:
            upsert_week(s, s.attendance)  # this week's reading joins the history
    try:
        recompute(s, "data_updated" if numeric else "profile_edited")
        audit(g.user, "student.updated", f"{s.code}: {', '.join(sorted(d))}")
        db.session.commit()
    except IntegrityError:
        db.session.rollback()
        raise ApiError("conflict", "A student with this name already exists in that course.", 409)
    return jsonify({"student": student_json(s, get_rules())})


@api.get("/students/<int:sid>/assessments")
@require()
def students_history(sid):
    s = get_student(sid, g.user)
    rows = Assessment.query.filter_by(student_id=s.id).order_by(Assessment.id.desc()).all()
    return jsonify({"assessments": [{"score": r.score, "category": r.category, "factors": r.factors, "reason": r.reason, "created_at": iso(r.created_at)} for r in rows]})


@api.get("/students/<int:sid>/attendance")
@require()
def att_list(sid):
    s = get_student(sid, g.user)
    rows = AttendanceRecord.query.filter_by(student_id=s.id).order_by(AttendanceRecord.week_start).all()
    return jsonify({"attendance": [{"week_start": iso(r.week_start), "percent": r.percent} for r in rows]})


@api.post("/students/<int:sid>/attendance")
@require("admin", "faculty")
def att_add(sid):
    s, d, errs = get_student(sid, g.user), body(), {}
    p = pct(d, "percent", errs)
    if p is None and "percent" not in errs:
        errs["percent"] = "is required"
    try:
        wk = week_of(date.fromisoformat(d["week_start"])) if d.get("week_start") else week_of(date.today())
        if wk > date.today():
            errs["week_start"] = "cannot be in the future"
    except (TypeError, ValueError):
        wk = None
        errs["week_start"] = "must be a date like 2026-06-01"
    check(errs)
    rec = upsert_week(s, p, wk)
    latest = AttendanceRecord.query.filter_by(student_id=s.id).order_by(AttendanceRecord.week_start.desc()).first()
    if latest.id == rec.id:  # only the newest week changes the current figure and score
        s.attendance, s.data_updated_at = p, utcnow()
        recompute(s, "data_updated")
    audit(g.user, "attendance.recorded", f"{s.code} week {iso(wk)}")
    db.session.commit()
    return jsonify({"student": student_json(s, get_rules())}), 201


@api.post("/students/import")
@require("admin")
def students_import():
    d = body()
    if not isinstance(d.get("csv"), str) or not d["csv"].strip():
        raise ApiError("validation", "Send the CSV text in a 'csv' field.", 422)
    existing = {(n.lower(), c.lower()) for n, c in db.session.query(Student.name, Student.course)}
    rows = parse_import(d["csv"], existing)
    good = [r for r in rows if r["ok"]]
    summary = {"rows": rows, "valid": len(good), "rejected": len(rows) - len(good)}
    if request.args.get("preview") == "1":
        return jsonify({**summary, "imported": 0})
    try:
        for r in good:  # one transaction: all valid rows or none
            s = Student(code="pending-" + secrets.token_hex(6), **r["data"])
            db.session.add(s)
            db.session.flush()
            s.code = f"S{1000 + s.id}"
            if s.attendance is not None:
                upsert_week(s, s.attendance)
            recompute(s, "imported")
        audit(g.user, "student.import", f"{len(good)} added, {len(rows) - len(good)} rejected")
        db.session.commit()
    except IntegrityError:
        db.session.rollback()
        raise ApiError("conflict", "Import failed and nothing was saved.", 409)
    return jsonify({**summary, "imported": len(good)}), 201


@api.get("/students/export.csv")
@require()
def students_export():
    out = io.StringIO()
    w = csv.writer(out)
    w.writerow(["code", "name", "course", "attendance", "marks", "assignments", "risk_score", "risk_category", "outdated"])
    rules = get_rules()
    for s in scoped(g.user).order_by(Student.id):
        w.writerow([csv_cell(x) for x in (s.code, s.name, s.course, s.attendance, s.marks, s.assignments, s.risk_score, s.risk_category, risk.is_stale(s.data_updated_at, rules))])
    audit(g.user, "student.export")
    db.session.commit()
    return Response(out.getvalue(), mimetype="text/csv", headers={"Content-Disposition": "attachment; filename=students.csv"})


# ---- interventions ----------------------------------------------------------
@api.get("/interventions")
@require()
def iv_list():
    ids = [x for (x,) in scoped(g.user).with_entities(Student.id)]
    q = Intervention.query.filter(Intervention.student_id.in_(ids))
    for k in ("status", "priority"):
        if request.args.get(k):
            q = q.filter(getattr(Intervention, k) == request.args[k])
    if request.args.get("assignee_id", "").isdigit():
        q = q.filter(Intervention.assignee_id == int(request.args["assignee_id"]))
    today = date.today()
    rows = q.order_by(Intervention.due_date).all()
    return jsonify({"interventions": [{**iv_json(i), "overdue": i.status in ("planned", "in_progress") and i.due_date < today} for i in rows]})


@api.post("/interventions")
@require("admin", "faculty", "support")
def iv_create():
    d, errs = body(), {}
    s = get_student(d.get("student_id") if isinstance(d.get("student_id"), int) else -1, g.user)
    cat, desc = text(d, "category", 2, 30, errs), text(d, "description", 5, 1000, errs)
    prio = d.get("priority", "medium")
    if prio not in ("low", "medium", "high"):
        errs["priority"] = "must be low, medium or high"
    try:
        due = date.fromisoformat(d.get("due_date", ""))
        if due < date.today():
            errs["due_date"] = "must be today or later"
    except (TypeError, ValueError):
        due = None
        errs["due_date"] = "must be a date like 2026-12-31"
    assignee = db.session.get(User, d["assignee_id"]) if isinstance(d.get("assignee_id"), int) else g.user
    if not assignee or not assignee.active:
        errs["assignee_id"] = "must be an active staff member"
    check(errs)
    i = Intervention(student_id=s.id, category=cat, priority=prio, assignee_id=assignee.id, created_by=g.user.id, description=desc, due_date=due)
    db.session.add(i)
    db.session.flush()
    if assignee.id != g.user.id:
        notify([assignee], f"assigned:{i.id}", f"New intervention for {s.name}", f"{cat} support is due {due.isoformat()}.", s.id)
    audit(g.user, "intervention.created", f"#{i.id} for {s.code}")
    db.session.commit()
    return jsonify({"intervention": iv_json(i)}), 201


@api.patch("/interventions/<int:iid>")
@require("admin", "faculty", "support")
def iv_update(iid):
    i, d = db.session.get(Intervention, iid), body()
    if not i:
        raise ApiError("not_found", "Intervention not found.", 404)
    s = get_student(i.student_id, g.user)
    if g.user.role == "faculty" and i.assignee_id != g.user.id:
        raise ApiError("forbidden", "Only the assignee can update this intervention.", 403)
    if "notes" in d:
        errs = {}
        i.notes = text(d, "notes", 1, 1000, errs, required=False)
        check(errs)
    new = d.get("status")
    if new is not None:
        if new not in IV_TRANSITIONS.get(i.status, set()):
            raise ApiError("conflict", f"Cannot move from {i.status} to {new}.", 409)
        if new == "completed":
            if d.get("outcome") not in ("improved", "no_change", "declined"):
                raise ApiError("validation", "Completing needs an outcome: improved, no_change or declined.", 422, {"outcome": "required"})
            i.outcome, i.completed_at = d["outcome"], utcnow()
            notify(recipients(s), f"completed:{i.id}", f"Intervention completed: {s.name}", f"Outcome: {i.outcome}.", s.id)
        i.status = new
    audit(g.user, "intervention.updated", f"#{i.id}: {i.status}")
    db.session.commit()
    return jsonify({"intervention": iv_json(i)})


# ---- notifications ----------------------------------------------------------
@api.get("/notifications")
@require()
def notif_list():
    run_overdue_rule()  # defined rule; no background scheduler is required
    q = Notification.query.filter_by(user_id=g.user.id)
    if request.args.get("unread") == "1":
        q = q.filter_by(read=False)
    rows = q.order_by(Notification.id.desc()).limit(100).all()
    return jsonify({"unread": Notification.query.filter_by(user_id=g.user.id, read=False).count(),
                    "notifications": [{"id": n.id, "title": n.title, "body": n.body, "student_id": n.student_id, "read": n.read, "created_at": iso(n.created_at)} for n in rows]})


@api.post("/notifications/<int:nid>/read")
@require()
def notif_read(nid):
    n = Notification.query.filter_by(id=nid, user_id=g.user.id).first()
    if not n:
        raise ApiError("not_found", "Notification not found.", 404)
    n.read = True
    db.session.commit()
    return jsonify({"ok": True})


@api.post("/notifications/read-all")
@require()
def notif_read_all():
    Notification.query.filter_by(user_id=g.user.id, read=False).update({"read": True})
    db.session.commit()
    return jsonify({"ok": True})


# ---- rules, reports, audit --------------------------------------------------
@api.get("/rules")
@require()
def rules_get():
    return jsonify({"rules": get_rules()})


@api.put("/rules")
@require("admin")
def rules_put():
    clean, errs = risk.validate_rules(body())
    check(errs)
    row = db.session.get(Setting, "rules")
    if row:
        row.value = clean
    else:
        db.session.add(Setting(key="rules", value=clean))
    changed = 0
    for s in Student.query:  # one transaction for the whole recalculation
        changed += recompute(s, "rules_changed", clean)
    audit(g.user, "rules.updated", f"{changed} students recalculated")
    db.session.commit()
    return jsonify({"rules": clean, "recalculated": changed})


@api.get("/reports/summary")
@require()
def summary():
    ids = [x for (x,) in scoped(g.user).with_entities(Student.id)]
    sq = Student.query.filter(Student.id.in_(ids))
    cats = dict(sq.with_entities(Student.risk_category, func.count()).group_by(Student.risk_category).all())
    courses = [{"course": c, "students": n, "average_score": round(a or 0, 1)} for c, n, a in sq.with_entities(Student.course, func.count(), func.avg(Student.risk_score)).group_by(Student.course)]
    factors = {}
    for s in sq:
        for f in s.risk_factors or []:
            if f["points"]:
                factors[f["factor"]] = factors.get(f["factor"], 0) + 1
    ivq = Intervention.query.filter(Intervention.student_id.in_(ids))
    return jsonify({"students": len(ids), "by_category": cats, "by_course": courses, "factors": factors,
                    "interventions_by_status": dict(ivq.with_entities(Intervention.status, func.count()).group_by(Intervention.status).all()),
                    "outcomes": dict(ivq.filter(Intervention.status == "completed").with_entities(Intervention.outcome, func.count()).group_by(Intervention.outcome).all()),
                    "note": "Outcome counts come from recorded interventions only; they are not a measure of effectiveness."})


@api.get("/reports/attendance-trend")
@require()
def attendance_trend():
    ids = [x for (x,) in scoped(g.user).with_entities(Student.id)]
    rows = (db.session.query(AttendanceRecord.week_start, func.avg(AttendanceRecord.percent), func.count())
            .filter(AttendanceRecord.student_id.in_(ids)).group_by(AttendanceRecord.week_start)
            .order_by(AttendanceRecord.week_start.desc()).limit(12).all())
    return jsonify({"weeks": [{"week_start": iso(w), "average": round(a, 1), "students": n} for w, a, n in reversed(rows)],
                    "note": "Averages use only the students who have a reading that week."})


@api.get("/audit")
@require("admin")
def audit_list():
    rows = Audit.query.order_by(Audit.id.desc()).limit(200).all()
    return jsonify({"events": [{"id": a.id, "actor_id": a.actor_id, "action": a.action, "detail": a.detail, "created_at": iso(a.created_at)} for a in rows]})


# ---- profile, preferences, bulk actions -------------------------------------
DEFAULT_PREFS = {"risk": True, "overdue": True, "assign": True}


@api.patch("/auth/profile")
@require(*ALL_ROLES)
def profile_update():
    errs = {}
    name = text(body(), "name", 2, 120, errs)
    check(errs)
    g.user.name = name
    audit(g.user, "auth.profile_updated")
    db.session.commit()
    return jsonify({"user": g.user.to_json()})


@api.get("/auth/prefs")
@require()
def prefs_get():
    return jsonify({"prefs": {**DEFAULT_PREFS, **(g.user.prefs or {})}})


@api.put("/auth/prefs")
@require()
def prefs_put():
    cur = {**DEFAULT_PREFS, **(g.user.prefs or {})}
    for k, v in body().items():
        if k not in DEFAULT_PREFS or not isinstance(v, bool):
            raise ApiError("validation", "Unknown preference, or the value is not true or false.", 422, {k: "invalid"})
        cur[k] = v
    g.user.prefs = cur
    db.session.commit()
    return jsonify({"prefs": cur})


@api.post("/interventions/bulk")
@require("admin", "faculty", "support")
def iv_bulk():
    d, errs = body(), {}
    ids = d.get("student_ids")
    if not isinstance(ids, list) or not 1 <= len(ids) <= 100 or not all(isinstance(i, int) and not isinstance(i, bool) for i in ids):
        raise ApiError("validation", "Choose between 1 and 100 students.", 422, {"student_ids": "invalid"})
    students = [get_student(i, g.user) for i in dict.fromkeys(ids)]  # one out-of-scope id fails the whole request
    cat, desc = text(d, "category", 2, 30, errs), text(d, "description", 5, 1000, errs)
    prio = d.get("priority", "medium")
    if prio not in ("low", "medium", "high"):
        errs["priority"] = "must be low, medium or high"
    try:
        due = date.fromisoformat(d.get("due_date", ""))
        if due < date.today():
            errs["due_date"] = "must be today or later"
    except (TypeError, ValueError):
        due = None
        errs["due_date"] = "must be a date like 2026-12-31"
    assignee = db.session.get(User, d["assignee_id"]) if isinstance(d.get("assignee_id"), int) else g.user
    if not assignee or not assignee.active:
        errs["assignee_id"] = "must be an active staff member"
    check(errs)
    made = []
    for s in students:  # one transaction: all of them or none
        i = Intervention(student_id=s.id, category=cat, priority=prio, assignee_id=assignee.id, created_by=g.user.id, description=desc, due_date=due)
        db.session.add(i)
        db.session.flush()
        made.append(i)
        if assignee.id != g.user.id:
            notify([assignee], f"assigned:{i.id}", f"New intervention for {s.name}", f"{cat} support is due {due.isoformat()}.", s.id)
    audit(g.user, "intervention.bulk_created", f"{len(made)} interventions")
    db.session.commit()
    return jsonify({"created": len(made), "interventions": [iv_json(i) for i in made]}), 201




# =============================================================================
# PDF reports (a small built-in writer, no extra libraries)
# =============================================================================
import zlib  # noqa: E402

NAVY, BLUE, GREY, INK = (0.07, 0.15, 0.33), (0.15, 0.39, 0.92), (0.4, 0.45, 0.55), (0.06, 0.09, 0.16)
RISK_RGB = {"high": (0.73, 0.11, 0.11), "medium": (0.85, 0.47, 0.02), "low": (0.09, 0.64, 0.29), "incomplete": (0.58, 0.64, 0.72)}


class Pdf:
    """Minimal A4 PDF writer: text, tables, bars, page breaks and a footer. Standard fonts only,
    so characters outside Western European alphabets print as '?'."""
    W, H, M = 595, 842, 50

    def __init__(self, title):
        self.title, self.pages = title, []
        self.new_page()

    def new_page(self):
        self.ops = []
        self.pages.append(self.ops)
        self.y = self.H - self.M

    @staticmethod
    def esc(s):
        s = re.sub(r"[\r\n\t]+", " ", str(s if s is not None else ""))
        s = s.encode("latin-1", "replace").decode("latin-1")
        return s.replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")

    def text(self, x, y, s, size=10, bold=False, color=INK):
        self.ops.append("BT /F%d %s Tf %.3f %.3f %.3f rg %.1f %.1f Td (%s) Tj ET" % (2 if bold else 1, size, *color, x, y, self.esc(s)))

    def rect(self, x, y, w, h, color):
        self.ops.append("%.3f %.3f %.3f rg %.1f %.1f %.1f %.1f re f" % (*color, x, y, w, h))

    def hline(self, y, color=(0.88, 0.9, 0.93)):
        self.ops.append("%.3f %.3f %.3f RG 0.6 w %d %.1f m %d %.1f l S" % (*color, self.M, y, self.W - self.M, y))

    def need(self, h):
        if self.y - h < self.M + 24:
            self.new_page()

    @staticmethod
    def fit(s, width, size):
        s = re.sub(r"\s+", " ", str(s if s is not None else ""))
        n = max(3, int(width / (size * 0.55)))
        return s if len(s) <= n else s[: n - 3] + "..."

    def banner(self, title, sub):
        self.rect(0, self.H - 96, self.W, 96, NAVY)
        self.text(self.M, self.H - 52, title, 21, True, (1, 1, 1))
        self.text(self.M, self.H - 74, self.fit(sub, self.W - 2 * self.M, 10), 10, False, (0.78, 0.84, 0.96))
        self.y = self.H - 96 - 24

    def heading(self, s, size=13):
        self.need(size + 30)
        self.y -= size + 8
        self.text(self.M, self.y, s, size, True, NAVY)
        self.y -= 6

    def para(self, s, size=10, color=INK):
        n = int((self.W - 2 * self.M) / (size * 0.5))
        line = ""
        for word in str(s).split():
            if len(line) + len(word) + 1 > n:
                self.need(size + 5)
                self.y -= size + 4
                self.text(self.M, self.y, line, size, False, color)
                line = word
            else:
                line = (line + " " + word).strip()
        if line:
            self.need(size + 5)
            self.y -= size + 4
            self.text(self.M, self.y, line, size, False, color)

    def kpis(self, items):
        self.need(70)
        w = (self.W - 2 * self.M - 12 * (len(items) - 1)) / len(items)
        top = self.y - 8
        for i, (num, label, col) in enumerate(items):
            x = self.M + i * (w + 12)
            self.rect(x, top - 52, w, 52, (0.95, 0.96, 0.98))
            self.rect(x, top - 52, 3, 52, col)
            self.text(x + 12, top - 27, num, 20, True, col)
            self.text(x + 12, top - 43, self.fit(label, w - 14, 8.5), 8.5, False, GREY)
        self.y = top - 52 - 10

    def bar(self, parts):
        total = sum(v for v, _ in parts) or 1
        self.need(24)
        x, w = self.M, self.W - 2 * self.M
        self.y -= 16
        for v, col in parts:
            if v:
                self.rect(x, self.y, w * v / total, 12, col)
                x += w * v / total
        self.y -= 6

    def table(self, headers, rows, widths, size=8.5):
        scale = (self.W - 2 * self.M) / sum(widths)
        widths = [w * scale for w in widths]

        def head():
            self.need(24)
            self.y -= 18
            self.rect(self.M, self.y - 4, self.W - 2 * self.M, 17, (0.92, 0.94, 0.98))
            x = self.M
            for h, w in zip(headers, widths):
                self.text(x + 4, self.y, self.fit(h, w - 6, size), size, True, NAVY)
                x += w
        head()
        for row in rows:
            if self.y - 20 < self.M + 24:
                self.new_page()
                head()
            self.y -= 16
            x = self.M
            for cell, w in zip(row, widths):
                col = INK
                if isinstance(cell, tuple):
                    cell, col = cell
                self.text(x + 4, self.y, self.fit(cell, w - 6, size), size, False, col)
                x += w
            self.hline(self.y - 5)
        self.y -= 8
        if not rows:
            self.para("Nothing to show.", 9, GREY)

    def build(self):
        n = len(self.pages)
        for i, ops in enumerate(self.pages):
            ops.append("BT /F1 7.5 Tf 0.4 0.45 0.55 rg %d 26 Td (%s) Tj ET" % (self.M, self.esc("DropoutAlert - confidential student information - indicators for human review, not predictions - " + date.today().isoformat())))
            ops.append("BT /F1 7.5 Tf 0.4 0.45 0.55 rg %d 26 Td (Page %d of %d) Tj ET" % (self.W - self.M - 40, i + 1, n))
        objs = [b"<< /Type /Catalog /Pages 2 0 R >>",
                ("<< /Type /Pages /Kids [%s] /Count %d >>" % (" ".join("%d 0 R" % (6 + 2 * i) for i in range(n)), n)).encode(),
                b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>",
                b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>"]
        for i, ops in enumerate(self.pages):
            data = zlib.compress("\n".join(ops).encode("latin-1"))
            objs.append(b"<< /Length %d /Filter /FlateDecode >>\nstream\n" % len(data) + data + b"\nendstream")
            objs.append(("<< /Type /Page /Parent 2 0 R /MediaBox [0 0 %d %d] /Resources << /Font << /F1 3 0 R /F2 4 0 R >> >> /Contents %d 0 R >>" % (self.W, self.H, 5 + 2 * i)).encode())
        out, offs = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n"), []
        for i, o in enumerate(objs):
            offs.append(len(out))
            out += b"%d 0 obj\n" % (i + 1) + o + b"\nendobj\n"
        xref = len(out)
        out += b"xref\n0 %d\n0000000000 65535 f \n" % (len(objs) + 1)
        for o in offs:
            out += b"%010d 00000 n \n" % o
        out += b"trailer\n<< /Size %d /Root 1 0 R /Info << /Title (%s) >> >>\nstartxref\n%d\n%%%%EOF\n" % (len(objs) + 1, self.esc(self.title).encode("latin-1"), xref)
        return bytes(out)


def pdf_response(pdf, name):
    safe = re.sub(r"[^A-Za-z0-9_.-]", "_", name)
    return Response(pdf.build(), mimetype="application/pdf", headers={"Content-Disposition": f'attachment; filename="{safe}"'})


def fnum(v):
    return "-" if v is None else f"{v:g}"


def pdf_summary(u):
    rules, today = get_rules(), date.today().isoformat()
    L = scoped(u).order_by(Student.id).all()
    cats = {k: sum(1 for s in L if s.risk_category == k) for k in ("high", "medium", "low", "incomplete")}
    scope = {"admin": "all students", "support": "all students", "faculty": "your assigned courses"}[u.role]
    p = Pdf("DropoutAlert summary report")
    p.banner("Student support summary", f"{len(L)} students in scope ({scope}). Generated {today} for {u.name}.")
    p.kpis([(str(len(L)), "Students", BLUE), (str(cats["high"]), "High risk", RISK_RGB["high"]), (str(cats["medium"]), "Medium risk", RISK_RGB["medium"]), (str(cats["low"] + cats["incomplete"]), "Low or incomplete", RISK_RGB["low"])])
    p.bar([(cats[k], RISK_RGB[k]) for k in ("high", "medium", "low", "incomplete")])
    p.para("Bar order: high, medium, low, incomplete data. Records not updated for more than %d days are marked outdated." % rules["stale_days"], 8.5, GREY)
    by = {}
    for s in L:
        by.setdefault(s.course, []).append(s)
    p.heading("By course")
    p.table(["Course", "Students", "Average score", "High risk"], [[c, len(v), "%.1f" % (sum(s.risk_score or 0 for s in v) / len(v)), sum(1 for s in v if s.risk_category == "high")] for c, v in sorted(by.items())], [5, 1.5, 2, 1.5])
    fac = {}
    for s in L:
        for f in s.risk_factors or []:
            if f["points"]:
                fac[f["factor"]] = fac.get(f["factor"], 0) + 1
    p.heading("Main contributing factors")
    p.table(["Factor", "Students with points"], [[k, v] for k, v in sorted(fac.items(), key=lambda x: -x[1])], [5, 3])
    ids = [s.id for s in L]
    ivs = Intervention.query.filter(Intervention.student_id.in_(ids)).all() if ids else []
    st = {k: sum(1 for i in ivs if i.status == k) for k in ("planned", "in_progress", "completed", "cancelled")}
    oc = {k: sum(1 for i in ivs if i.outcome == k) for k in ("improved", "no_change", "declined")}
    p.heading("Interventions")
    p.para("Planned %d, in progress %d, completed %d, cancelled %d. Outcomes of completed work: improved %d, no change %d, declined %d." % (st["planned"], st["in_progress"], st["completed"], st["cancelled"], oc["improved"], oc["no_change"], oc["declined"]), 9.5)
    p.para("Outcome counts come from recorded interventions only and are not a measure of how well support works.", 8.5, GREY)
    attn = sorted([s for s in L if s.risk_category != "low"], key=lambda s: -(s.risk_score or 0))[:40]
    p.heading("Students who may need attention (top %d)" % len(attn))
    p.table(["Student", "Course", "Attend.", "Marks", "Assign.", "Score", "Category"],
            [[s.name, s.course, fnum(s.attendance), fnum(s.marks), fnum(s.assignments), fnum(s.risk_score), (s.risk_category + (", outdated" if risk.is_stale(s.data_updated_at, rules) else ""), RISK_RGB.get(s.risk_category, INK))] for s in attn], [3, 3.2, 1.2, 1.2, 1.2, 1.1, 2.4])
    p.heading("How to read this report")
    p.para("Scores add points for low attendance, marks and assignment completion using the rules set by your administrators (medium from %g, high from %g). They are illustrative indicators that suggest who may benefit from a conversation. They are not predictions of dropout, and every decision needs human review." % (rules["medium"], rules["high"]), 9)
    return p


def pdf_student(s, u):
    rules = get_rules()
    p = Pdf(f"Student report {s.code}")
    p.banner(s.name, f"{s.code}, {s.course}. Generated {date.today().isoformat()} for {u.name}.")
    cat = s.risk_category or "incomplete"
    p.kpis([(fnum(s.attendance) + ("%" if s.attendance is not None else ""), "Attendance", BLUE), (fnum(s.marks) + ("%" if s.marks is not None else ""), "Marks", BLUE), (fnum(s.assignments) + ("%" if s.assignments is not None else ""), "Assignments", BLUE), (fnum(s.risk_score), "Risk score: " + cat, RISK_RGB.get(cat, INK))])
    stale = risk.is_stale(s.data_updated_at, rules)
    p.para("Data last updated %s UTC.%s%s" % (s.data_updated_at.strftime("%Y-%m-%d %H:%M"), " This record is outdated; confirm the figures before acting." if stale else "", (" Missing: " + ", ".join(s.risk_missing) + ".") if s.risk_missing else ""), 9, GREY)
    p.heading("Why this score")
    p.table(["Factor", "Value", "Points added"], [[f["factor"], ("-" if f["value"] is None else "%g%%" % f["value"]), ("no data" if f["points"] is None else f["points"])] for f in (s.risk_factors or [])], [4, 2, 2])
    hist = Assessment.query.filter_by(student_id=s.id).order_by(Assessment.id.desc()).limit(15).all()
    p.heading("Score history")
    p.table(["When (UTC)", "Reason", "Score", "Category"], [[h.created_at.strftime("%Y-%m-%d %H:%M"), h.reason.replace("_", " "), fnum(h.score), (h.category, RISK_RGB.get(h.category, INK))] for h in hist], [3, 3.5, 1.5, 2])
    att = AttendanceRecord.query.filter_by(student_id=s.id).order_by(AttendanceRecord.week_start.desc()).limit(12).all()
    p.heading("Attendance by week")
    p.table(["Week starting", "Attendance"], [[a.week_start.isoformat(), "%g%%" % a.percent] for a in att], [3, 3])
    ivs = Intervention.query.filter_by(student_id=s.id).order_by(Intervention.due_date.desc()).all()
    p.heading("Interventions")
    p.table(["Support", "Priority", "Status", "Due", "Outcome", "Plan"], [[i.category, i.priority, i.status.replace("_", " "), i.due_date.isoformat(), (i.outcome or "-").replace("_", " "), i.description] for i in ivs], [2, 1.4, 1.6, 1.7, 1.6, 5])
    p.para("An indicator for review, not a prediction. Check the data and the student's context before acting.", 8.5, GREY)
    return p


def pdf_self(s):
    p = Pdf("My progress report")
    p.banner("My progress", f"{s.name}, {s.course}. Generated {date.today().isoformat()}.")
    p.kpis([(fnum(s.attendance) + ("%" if s.attendance is not None else ""), "Attendance", BLUE), (fnum(s.marks) + ("%" if s.marks is not None else ""), "Marks", BLUE), (fnum(s.assignments) + ("%" if s.assignments is not None else ""), "Assignments", BLUE)])
    p.para("These figures come from your college records, last updated %s UTC. If something looks wrong, tell your faculty mentor." % s.data_updated_at.strftime("%Y-%m-%d"), 9, GREY)
    att = AttendanceRecord.query.filter_by(student_id=s.id).order_by(AttendanceRecord.week_start.desc()).limit(12).all()
    p.heading("Attendance by week")
    p.table(["Week starting", "Attendance"], [[a.week_start.isoformat(), "%g%%" % a.percent] for a in att], [3, 3])
    plan = Intervention.query.filter(Intervention.student_id == s.id, Intervention.status != "cancelled").order_by(Intervention.due_date.desc()).all()
    p.heading("Your support plan")
    p.table(["Support", "Status", "Follow-up date"], [[i.category, i.status.replace("_", " "), i.due_date.isoformat()] for i in plan], [3, 2, 2])
    p.heading("Where to get help")
    for line in get_resources().splitlines():
        if line.strip():
            p.para("- " + line.strip(), 9.5)
    return p


# =============================================================================
# More API: student view, PDF downloads, saved views, student help text
# =============================================================================
DEFAULT_RESOURCES = ("Talk to your faculty mentor or class teacher if you are finding things difficult.\n"
                     "The student support team can help with attendance, studies and personal matters.\n"
                     "You can ask for help at any time. Asking early is a good thing.")


def get_resources():
    row = db.session.get(Setting, "resources")
    return row.value if row and isinstance(row.value, str) else DEFAULT_RESOURCES


@api.get("/resources")
@require(*ALL_ROLES)
def resources_get():
    return jsonify({"text": get_resources()})


@api.put("/resources")
@require("admin")
def resources_put():
    t = body().get("text")
    if not isinstance(t, str) or not 1 <= len(t.strip()) <= 1500 or re.search(r'[<>&"]', t):
        raise ApiError("validation", "Write 1 to 1500 characters without < > & or quotes.", 422, {"text": "invalid"})
    row = db.session.get(Setting, "resources")
    if row:
        row.value = t.strip()
    else:
        db.session.add(Setting(key="resources", value=t.strip()))
    audit(g.user, "resources.updated")
    db.session.commit()
    return jsonify({"text": t.strip()})


def my_student():
    s = db.session.get(Student, g.user.student_id) if g.user.student_id else None
    if not s:
        raise ApiError("not_found", "Your account is not linked to a student record yet. Ask the administrator.", 404)
    return s


@api.get("/me/student")
@require("student")
def me_student():
    """A student sees only their own figures. No risk score or category, no staff notes."""
    s = my_student()
    att = AttendanceRecord.query.filter_by(student_id=s.id).order_by(AttendanceRecord.week_start).all()
    plan = Intervention.query.filter(Intervention.student_id == s.id, Intervention.status != "cancelled").order_by(Intervention.due_date).all()
    return jsonify({"student": {"name": s.name, "course": s.course, "attendance": s.attendance, "marks": s.marks, "assignments": s.assignments, "updated": iso(s.data_updated_at)},
                    "attendance": [{"week_start": iso(a.week_start), "percent": a.percent} for a in att],
                    "support": [{"category": i.category, "status": i.status, "due_date": iso(i.due_date)} for i in plan],
                    "resources": get_resources()})


@api.get("/me/report.pdf")
@require("student")
def me_report():
    s = my_student()
    audit(g.user, "report.self")
    db.session.commit()
    return pdf_response(pdf_self(s), "my-progress.pdf")


@api.get("/reports/summary.pdf")
@require()
def summary_pdf():
    audit(g.user, "report.summary")
    db.session.commit()
    return pdf_response(pdf_summary(g.user), f"dropoutalert-summary-{date.today().isoformat()}.pdf")


@api.get("/students/<int:sid>/report.pdf")
@require()
def student_pdf(sid):
    s = get_student(sid, g.user)
    audit(g.user, "report.student", s.code)
    db.session.commit()
    return pdf_response(pdf_student(s, g.user), f"student-{s.code}.pdf")


VIEW_FIELDS = ("q", "course", "category", "sort", "order")


def clean_view(p, errs):
    if not isinstance(p, dict):
        errs["params"] = "must be an object"
        return {}
    out = {k: p.get(k, "") for k in VIEW_FIELDS}
    out["sort"], out["order"] = out["sort"] or "name", out["order"] or "asc"
    if not all(isinstance(v, str) for v in out.values()) or len(out["q"]) > 100 or len(out["course"]) > 80:
        errs["params"] = "values must be short text"
    elif out["category"] not in ("", "high", "medium", "low", "incomplete") or out["sort"] not in SORTS or out["order"] not in ("asc", "desc"):
        errs["params"] = "unknown category, sort or order"
    return out


@api.get("/views")
@require()
def views_list():
    rows = SavedView.query.filter_by(user_id=g.user.id).order_by(SavedView.name).all()
    return jsonify({"views": [{"id": v.id, "name": v.name, "params": v.params} for v in rows]})


@api.post("/views")
@require()
def views_create():
    d, errs = body(), {}
    name = text(d, "name", 1, 60, errs)
    params = clean_view(d.get("params"), errs)
    check(errs)
    if SavedView.query.filter_by(user_id=g.user.id).count() >= 20:
        raise ApiError("conflict", "You can keep up to 20 saved views. Delete one first.", 409)
    v = SavedView(user_id=g.user.id, name=name, params=params)
    db.session.add(v)
    try:
        db.session.commit()
    except IntegrityError:
        db.session.rollback()
        raise ApiError("conflict", "You already have a saved view with that name.", 409)
    return jsonify({"view": {"id": v.id, "name": v.name, "params": v.params}}), 201


@api.delete("/views/<int:vid>")
@require()
def views_delete(vid):
    v = SavedView.query.filter_by(id=vid, user_id=g.user.id).first()  # only your own
    if not v:
        raise ApiError("not_found", "Saved view not found.", 404)
    db.session.delete(v)
    db.session.commit()
    return jsonify({"ok": True})


# =============================================================================
# Application factory, start-up tasks and command line
# =============================================================================
DEMO_STUDENTS = [("Aarthi R", "B.Sc Computer Science", 58, 38, 45), ("Karthik M", "B.Com", 82, 71, 90), ("Meena S", "BBA", 66, 52, 60),
                 ("Vignesh P", "B.E. Mechanical", 54, 44, 48), ("Divya L", "B.Sc Computer Science", 91, 83, 95), ("Arun K", "B.A. English", 72, 49, 70),
                 ("Lakshmi N", "B.Com", 78, 62, 80), ("Suresh B", "B.E. Civil", 59, 36, 52), ("Nisha T", "BBA", 88, 76, 85),
                 ("Prakash V", "B.E. Mechanical", 69, 58, 44), ("Harini D", "B.A. English", 95, 90, 98), ("Manoj G", "B.Sc Computer Science", 63, 41, 72),
                 ("Revathi A", "B.Com", 74, 66, 55), ("Gokul S", "B.E. Civil", 85, 57, 77), ("Sangeetha J", "BBA", 49, 33, 38), ("Ravi C", "B.Sc Computer Science", 80, 68, 92)]
IMG_URL = re.compile(r"^https://[A-Za-z0-9\-._~:/?#\[\]@!$&()*+,;=%]+$")


def _db_url():
    url = os.environ.get("DATABASE_URL", "sqlite:///dropoutalert.db")
    return "postgresql://" + url[len("postgres://"):] if url.startswith("postgres://") else url


def seed_demo_data(app):
    """FICTIONAL demo users and students. Production needs an explicit DEMO_PASSWORD."""
    pw = os.environ.get("DEMO_PASSWORD")
    if app.config["PRODUCTION"] and not pw:
        log.error("Not seeding demo data in production without DEMO_PASSWORD.")
        return False
    pw = pw or "demo1234"
    for email, name, role, courses in [("admin@dropoutalert.demo", "Admin", "admin", []),
                                       ("faculty@dropoutalert.demo", "Dr. Priya Nair", "faculty", ["B.Sc Computer Science", "BBA"]),
                                       ("support@dropoutalert.demo", "Ravi Menon", "support", [])]:
        if not User.query.filter_by(email=email).first():
            u = User(email=email, name=name, role=role, courses=courses, active=True)
            u.set_password(pw)
            db.session.add(u)
    for i, (n, c, a, m, asg) in enumerate(DEMO_STUDENTS, start=1):
        s = Student(code=f"S{1000 + i}", name=n, course=c, attendance=a, marks=m, assignments=asg)
        db.session.add(s)
        db.session.flush()
        tr = ((i * 7) % 5 - 2) * 0.9  # fictional history that ends at the current figure
        for k in range(6):
            db.session.add(AttendanceRecord(student_id=s.id, week_start=week_of(date.today()) - timedelta(weeks=5 - k), percent=round(max(30, min(100, a + (5 - k) * tr)), 1)))
        recompute(s, "seed")
    db.session.commit()
    return True


def bootstrap(app):
    email, pw = (os.environ.get("ADMIN_EMAIL") or "").strip().lower(), os.environ.get("ADMIN_PASSWORD")
    if email and pw and not User.query.filter_by(role="admin").first():
        try:
            check_password_strength(pw, email)
            u = User(email=email, name=os.environ.get("ADMIN_NAME", "Administrator"), role="admin", courses=[], active=True)
            u.set_password(pw)
            db.session.add(u)
            audit(None, "admin.bootstrap", email)
            db.session.commit()
            log.warning("First administrator created: %s. Remove ADMIN_PASSWORD from the environment now.", email)
        except ApiError:
            log.error("ADMIN_PASSWORD is too weak (8+ characters with a letter and a number). No administrator was created.")
    if os.environ.get("SEED_DEMO") == "1" and not Student.query.count():
        seed_demo_data(app)


def _index_html():
    url = os.environ.get("LOGIN_IMAGE_URL", "").strip()
    hero = ""
    if url and IMG_URL.match(url):
        hero = '.pnl{background-image:linear-gradient(160deg,rgba(11,29,74,.88),rgba(30,58,138,.72)),url("%s");background-size:cover;background-position:center}.pnl svg{display:none}' % url.replace('"', "%22")
    return INDEX_HTML.replace("/*HERO*/", hero)


def create_app(config=None):
    cfg = config or {}
    app = Flask(__name__, static_folder=None)
    prod = os.environ.get("APP_ENV") == "production"
    secret = cfg.get("SECRET_KEY") or os.environ.get("SECRET_KEY")
    if not secret:
        if prod:
            raise RuntimeError("SECRET_KEY must be set in production.")
        secret = secrets.token_hex(32)
        log.warning("SECRET_KEY is not set; using a random development key. Sessions end when the app restarts.")
    public = cfg.get("PUBLIC_URL") or os.environ.get("PUBLIC_URL")
    if prod and not public:
        raise RuntimeError("PUBLIC_URL must be set in production (it is used in password reset emails).")
    uri = cfg.get("SQLALCHEMY_DATABASE_URI") or _db_url()
    app.config.update(
        SECRET_KEY=secret, SQLALCHEMY_DATABASE_URI=uri, PUBLIC_URL=public, PRODUCTION=prod,
        SESSION_COOKIE_HTTPONLY=True, SESSION_COOKIE_SAMESITE="Lax", SESSION_COOKIE_SECURE=prod or os.environ.get("COOKIE_SECURE") == "1",
        PERMANENT_SESSION_LIFETIME=timedelta(hours=int(os.environ.get("SESSION_HOURS", "8"))), MAX_CONTENT_LENGTH=1_000_000,
    )
    if not uri.startswith("sqlite"):
        app.config["SQLALCHEMY_ENGINE_OPTIONS"] = {"pool_pre_ping": True}
    app.config.update(cfg)
    if os.environ.get("TRUST_PROXY") == "1":
        app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)
    db.init_app(app)
    app.outbox = []
    register_errors(app)

    @app.after_request
    def headers(resp):
        resp.headers.setdefault("X-Content-Type-Options", "nosniff")
        resp.headers.setdefault("Cache-Control", "no-store")
        resp.headers.setdefault("Referrer-Policy", "same-origin")
        if app.config["SESSION_COOKIE_SECURE"]:
            resp.headers.setdefault("Strict-Transport-Security", "max-age=31536000")
        if resp.mimetype == "text/html":
            img = "img-src 'self' data: https:" if os.environ.get("LOGIN_IMAGE_URL") else "img-src 'self' data:"
            resp.headers.setdefault("Content-Security-Policy", f"default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline' https://fonts.googleapis.com; font-src https://fonts.gstatic.com; {img}; frame-ancestors 'none'")
        return resp

    @app.get("/")
    def index():
        return Response(_index_html(), mimetype="text/html")

    @app.get("/static/app.js")
    def app_js():
        r = Response(APP_JS, mimetype="text/javascript")
        r.headers["Cache-Control"] = "no-cache"
        return r

    @app.get("/healthz")
    def healthz():
        db.session.execute(db.text("SELECT 1"))
        return jsonify({"status": "ok"})

    app.register_blueprint(api)
    register_cli(app)
    with app.app_context():
        startup(app)
    return app


def startup(app):
    """Create tables and first-run data. Several workers may start at once and race each other,
    so a clash just means another worker already did the job: roll back, wait, and check again."""
    for attempt in range(4):
        try:
            db.create_all()
            bootstrap(app)
            return
        except (IntegrityError, OperationalError, ProgrammingError):
            db.session.rollback()
            time.sleep(0.4 * (attempt + 1))
    log.error("Start-up tasks could not finish. Check the database connection and permissions.")


def register_cli(app):
    @app.cli.command("create-admin")
    @click.option("--email", prompt=True)
    @click.option("--name", prompt=True)
    @click.password_option()
    def create_admin(email, name, password):
        """Create an administrator (asks for the password without showing it)."""
        check_password_strength(password, email)
        u = User(email=email.strip().lower(), name=name, role="admin", active=True, courses=[])
        u.set_password(password)
        db.session.add(u)
        db.session.commit()
        click.echo("Administrator created.")

    @app.cli.command("seed-demo")
    def seed_demo():
        """Add FICTIONAL demo users and students to an empty database."""
        if Student.query.count():
            raise click.ClickException("The database already has students.")
        if not seed_demo_data(app):
            raise click.ClickException("Refused: set DEMO_PASSWORD to seed demo data in production.")
        click.echo("Demo data added. Fictional data only.")

    @app.cli.command("run-rules")
    def run_rules():
        """Create overdue follow-up notifications (safe to run from cron)."""
        click.echo(f"{run_overdue_rule()} notification(s) created.")


# =============================================================================
# Embedded web app (served at / and /static/app.js)
# =============================================================================
INDEX_HTML = r'''<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<link rel="icon" href="data:image/svg+xml,%3Csvg xmlns=%27http://www.w3.org/2000/svg%27 viewBox=%270 0 32 32%27%3E%3Cpath d=%27M16 2 28 7v9c0 7-5 12-12 14C9 28 4 23 4 16V7z%27 fill=%27%231e3a8a%27/%3E%3Cpath d=%27M16 9v8m0 4v.5%27 stroke=%27white%27 stroke-width=%273%27 stroke-linecap=%27round%27/%3E%3C/svg%3E">
<title>DropoutAlert – Student Dropout Early Warning System</title>
<link href="https://fonts.googleapis.com/css2?family=Source+Serif+4:wght@600;700&family=Inter:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--bg:#f5f7fa;--card:#fff;--ink:#0f172a;--mut:#64748b;--ln:#e2e8f0;--p:#1e3a8a;--p2:#2563eb;--pb:#e8eefc;--btn:#1e3a8a;--low:#15803d;--med:#b45309;--high:#b91c1c;--lowb:#dcfce7;--medb:#fef3c7;--highb:#fee2e2;--bar:#2563eb;color-scheme:light;padding-top:env(safe-area-inset-top,0px);padding-bottom:env(safe-area-inset-bottom,0px)}
:root[data-theme="dark"]{--bg:#0a1122;--card:#111a30;--ink:#e6edf8;--mut:#8fa0ba;--ln:#1f2c48;--p:#8fb0ff;--p2:#5b93ff;--pb:rgba(91,147,255,.15);--btn:#3b6fe8;--low:#5fd596;--med:#f2b552;--high:#ff8a8a;--lowb:rgba(95,213,150,.14);--medb:rgba(242,181,82,.14);--highb:rgba(255,138,138,.14);--bar:#5b93ff;color-scheme:dark}
*{box-sizing:border-box;margin:0}
html,body{height:100%}
body{font-family:Inter,system-ui,sans-serif;background:var(--bg);color:var(--ink);font-size:14px;line-height:1.5}
h1,h2,h3,.k{font-family:"Source Serif 4",Georgia,serif}
button,input,select{font:inherit;color:inherit}button{cursor:pointer}
:focus-visible{outline:2px solid var(--p2);outline-offset:2px}
.hide{display:none!important}
.btn{background:var(--btn);color:#fff;border:0;border-radius:9px;padding:10px 16px;font-weight:600;transition:transform .15s,filter .15s}.btn:hover{filter:brightness(1.12)}.btn:active{transform:scale(.97)}
.btn.s{background:var(--card);color:var(--ink);border:1px solid var(--ln)}
.link{background:none;border:0;color:var(--p2);font-weight:600;padding:0}.link:hover{text-decoration:underline}
.logo{display:flex;gap:9px;align-items:center;font:700 18px "Source Serif 4",serif;color:var(--p)}
/* auth */
#auth{min-height:100%;display:grid;grid-template-columns:1.05fr 1fr}
.pnl{position:relative;overflow:hidden;background:linear-gradient(160deg,#0b1d4a,#1e3a8a 60%,#1b5fa3);color:#fff;padding:44px;display:flex;flex-direction:column;justify-content:space-between;min-height:300px}
.pnl .logo{color:#fff}
.orb{position:absolute;width:420px;height:420px;border-radius:50%;right:-120px;top:-120px;background:radial-gradient(circle,rgba(96,165,250,.5),transparent 65%);animation:drift 14s ease-in-out infinite alternate}
.pnl svg{position:absolute;right:-30px;bottom:0;width:92%;max-width:640px}
.pnl svg *{stroke-dasharray:1;stroke-dashoffset:1;animation:draw 2.6s ease forwards}
.pnl svg *:nth-child(n+4){animation-delay:.5s}.pnl svg *:nth-child(n+8){animation-delay:1s}
.pnl>div,.pnl>.logo{position:relative}
.pnl h1{font-size:clamp(30px,3.6vw,46px);max-width:13ch;margin-bottom:12px}.pnl p{color:#c7d6f5;max-width:40ch}
.fm{display:flex;align-items:center;justify-content:center;padding:32px;background:var(--card)}
.fm>div{width:100%;max-width:360px;animation:rise .6s both}
.fm h2{font-size:30px}.sub{color:var(--mut);margin:4px 0 20px}
label{display:block;font-weight:600;font-size:12.5px;margin:14px 0 6px}
.field{width:100%;padding:11px 13px;border:1px solid var(--ln);border-radius:9px;background:var(--bg);transition:border-color .15s,box-shadow .15s}
.field:focus{outline:0;border-color:var(--p2);box-shadow:0 0 0 3px var(--pb)}
.pw{position:relative}.pw button{position:absolute;right:6px;top:6px;background:none;border:0;color:var(--mut);font-weight:600;padding:5px 8px;font-size:13px}
.row{display:flex;justify-content:space-between;align-items:center;margin:14px 0 18px;font-size:13.5px}.row label{margin:0;font-weight:400;display:flex;gap:7px;align-items:center}
.msg{padding:10px 12px;border-radius:9px;font-size:13.5px;margin-top:14px}.msg.err{background:var(--highb);color:var(--high)}.msg.ok{background:var(--lowb);color:var(--low)}
.fm .btn{width:100%;padding:12px}
.demo{margin-top:20px;padding:12px 14px;border:1px dashed var(--p2);border-radius:10px;background:var(--pb);font-size:13px}
/* app */
#app{display:grid;grid-template-columns:228px 1fr;min-height:100%}
aside{background:var(--card);border-right:1px solid var(--ln);padding:18px 12px;display:flex;flex-direction:column;gap:2px;position:sticky;top:0;height:100vh}
aside .logo{padding:0 8px 20px}
.nv{display:flex;align-items:center;gap:10px;width:100%;background:none;border:0;text-align:left;padding:9px 11px;border-radius:9px;color:var(--mut);font-weight:500;transition:background .15s,color .15s}
.nv:hover{background:var(--pb);color:var(--p)}.nv[aria-current="page"]{background:var(--pb);color:var(--p);font-weight:600;box-shadow:inset 3px 0 0 var(--p2)}
.nv svg{width:18px;height:18px;flex:none}
aside .gap{margin-top:14px;padding:0 11px 4px;font-size:12px;color:var(--mut)}
aside .foot{margin-top:auto;font-size:12px;color:var(--mut);padding:10px}
main{min-width:0}
.top{display:flex;align-items:center;gap:12px;padding:12px 28px;background:var(--card);border-bottom:1px solid var(--ln);position:sticky;top:0;z-index:5}
.sr{position:relative;flex:1;max-width:360px}.sr input{padding-left:36px}.sr svg{position:absolute;left:11px;top:11px;width:16px;height:16px;color:var(--mut)}
.ib{background:none;border:1px solid var(--ln);border-radius:9px;width:38px;height:38px;display:grid;place-items:center}.ib:hover{background:var(--pb)}
.av{width:32px;height:32px;border-radius:50%;background:var(--pb);color:var(--p);display:grid;place-items:center;font-weight:600;font-size:12px;flex:none}
.me{margin-left:auto;display:flex;align-items:center;gap:10px}
.page{padding:26px 28px 40px;max-width:1220px}
.ph{display:flex;justify-content:space-between;align-items:flex-end;gap:12px;flex-wrap:wrap;margin-bottom:20px}
.ph h1{font-size:30px}.lead{color:var(--mut)}
.grid{display:grid;grid-template-columns:repeat(12,1fr);gap:16px}
.c3{grid-column:span 3}.c4{grid-column:span 4}.c8{grid-column:span 8}.c12{grid-column:span 12}
.card{background:var(--card);border:1px solid var(--ln);border-radius:12px;padding:18px;min-width:0}
.card h2{font:600 15px Inter,sans-serif;margin-bottom:2px}.nt{color:var(--mut);font-size:12.5px;margin-bottom:12px}
.kpi{position:relative;overflow:hidden}.kpi:before{content:"";position:absolute;left:0;top:0;bottom:0;width:4px;background:var(--a,var(--p2))}
.kpi .k{font-size:36px;font-weight:700;line-height:1.1;display:block;margin-bottom:2px}.kpi span.l{color:var(--mut);font-size:13px}
.kpi{transition:transform .2s,box-shadow .2s}.kpi:hover{transform:translateY(-2px);box-shadow:0 8px 20px rgba(15,23,42,.1)}
.flush{padding:0;overflow:hidden}.flush .hd{padding:16px 18px 6px;display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:10px}
.chips{display:flex;gap:6px}.chip{border:1px solid var(--ln);background:var(--card);border-radius:99px;padding:4px 12px;font-size:12.5px;font-weight:500;color:var(--mut)}.chip[aria-pressed="true"]{background:var(--btn);border-color:var(--btn);color:#fff}
.tw{overflow-x:auto}table{width:100%;border-collapse:collapse;font-size:13px}th{text-align:left;color:var(--mut);font-weight:500;padding:9px 12px;background:var(--bg);border-bottom:1px solid var(--ln);white-space:nowrap}
td{padding:11px 12px;border-bottom:1px solid var(--ln)}tr.rw{cursor:pointer;transition:background .15s}tr.rw:hover{background:var(--pb)}
.nm{display:flex;align-items:center;gap:10px}
.p{display:inline-flex;gap:4px;align-items:center;border-radius:6px;padding:2px 8px;font-size:12px;font-weight:600;white-space:nowrap}
.p.high{background:var(--highb);color:var(--high)}.p.medium{background:var(--medb);color:var(--med)}.p.low{background:var(--lowb);color:var(--low)}
.trk{height:7px;background:var(--ln);border-radius:7px;overflow:hidden;min-width:60px}.trk i{display:block;height:100%;background:var(--bar);border-radius:7px;transform-origin:left;animation:grow .9s cubic-bezier(.2,.7,.2,1) both}
.stk{display:flex;height:16px;border-radius:8px;overflow:hidden;gap:2px;margin:6px 0 14px}.stk i{transform-origin:left;animation:grow 1s cubic-bezier(.2,.7,.2,1) both}
.lg{display:flex;align-items:center;gap:10px;padding:7px 0;border-top:1px solid var(--ln)}.lg .w{flex:1}
.note{font-size:12.5px;color:var(--mut);padding:11px 14px;border-left:3px solid var(--p2);background:var(--pb);border-radius:0 9px 9px 0;margin-top:18px}
.empty{padding:26px;text-align:center;color:var(--mut)}
.ph2{display:grid;place-items:center;text-align:center;padding:90px 20px;color:var(--mut)}.ph2 h2{font:700 24px "Source Serif 4",serif;color:var(--ink);margin-bottom:6px}
#drawer{position:fixed;inset:0 0 0 auto;width:min(430px,100%);background:var(--card);border-left:1px solid var(--ln);box-shadow:-20px 0 44px rgba(15,23,42,.2);padding:24px;transform:translateX(104%);transition:transform .3s cubic-bezier(.2,.7,.2,1);z-index:20;overflow:auto}
#drawer.open{transform:none}
.big{font:700 60px "Source Serif 4",serif;line-height:1}
.fac{margin:14px 0}.fac div.t{display:flex;justify-content:space-between;font-weight:500;margin-bottom:5px}
#toast{position:fixed;left:50%;bottom:78px;transform:translateX(-50%);background:var(--ink);color:var(--bg);padding:10px 16px;border-radius:10px;z-index:30;font-size:13.5px;max-width:90vw;animation:rise .25s both}
.tabbar{display:none}
.rise{animation:rise .55s cubic-bezier(.2,.7,.2,1) both;animation-delay:calc(var(--i,0)*70ms)}
.rt tr{animation:rise .5s both;animation-delay:calc(var(--i,0)*45ms + .3s)}
.dl{stroke-dasharray:1;stroke-dashoffset:1;animation:draw 1.4s .4s ease forwards}
.c6{grid-column:span 6}
.sort{background:none;border:0;color:inherit;font:inherit;font-weight:500;padding:0}.sort:hover{color:var(--p)}
tr.rd{cursor:pointer;transition:background .15s}tr.rd:hover{background:var(--pb)}
.fl{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:14px}.sel{width:auto;min-width:170px;background:var(--card)}
.pgn{display:flex;justify-content:space-between;align-items:center;padding:12px 18px;color:var(--mut);font-size:12.5px;border-top:1px solid var(--ln)}
.tabs{display:flex;gap:22px;border-bottom:1px solid var(--ln);margin:6px 0 18px;overflow-x:auto}.tabs button{background:none;border:0;padding:9px 0;color:var(--mut);font-weight:500;white-space:nowrap;border-bottom:2px solid transparent}.tabs button[aria-pressed="true"]{color:var(--p);border-color:var(--p2);font-weight:600}
.mt{position:relative}.tick{position:absolute;top:-3px;width:2px;height:13px;background:var(--ink);opacity:.45}
.back{background:none;border:0;color:var(--p2);font-weight:600;padding:0;margin-bottom:12px}
.hdr{display:flex;align-items:center;gap:16px;flex-wrap:wrap}.av.avl{width:56px;height:56px;font-size:18px}
.bars{display:flex;align-items:flex-end;gap:12px;height:160px;padding-top:10px}.bars div.b{flex:1;text-align:center}.bars i{display:block;background:var(--bar);border-radius:6px 6px 0 0;transform-origin:bottom;animation:growy .8s cubic-bezier(.2,.7,.2,1) both}
@keyframes growy{from{transform:scaleY(0)}to{transform:none}}
.bdg{margin-left:auto;background:var(--high);color:#fff;border-radius:99px;font-size:11px;padding:0 7px;font-weight:600;line-height:18px}
.p.t{background:var(--pb);color:var(--p)}
.al{display:flex;width:100%;gap:12px;padding:14px 18px;background:none;border:0;border-bottom:1px solid var(--ln);text-align:left;align-items:center;transition:background .15s}.al:hover{background:var(--pb)}.al .w{flex:1;min-width:0}.al small{display:block;color:var(--mut)}
.dot2{width:9px;height:9px;border-radius:50%;background:var(--p2);flex:none}
textarea.field{resize:vertical;font-family:inherit}
.wl{display:flex;align-items:center;gap:10px;padding:9px 0;border-top:1px solid var(--ln)}.wl .w{flex:1;min-width:0}.wl small{display:block;color:var(--mut)}
.sw{width:40px;height:22px;border-radius:99px;border:0;background:var(--ln);position:relative;flex:none;transition:background .2s}.sw:after{content:"";position:absolute;left:3px;top:3px;width:16px;height:16px;border-radius:50%;background:#fff;transition:transform .2s}.sw[aria-checked="true"]{background:var(--p2)}.sw[aria-checked="true"]:after{transform:translateX(18px)}
.c7{grid-column:span 7}.c5{grid-column:span 5}
.cf{display:grid;grid-template-columns:1.3fr 1fr 1fr 1fr 1fr;gap:8px;align-items:center;font-size:13px;margin-bottom:8px}.cf .field{padding:6px 8px}.cf small{color:var(--mut)}
.seg{display:flex;gap:8px;flex-wrap:wrap}
.lk{display:flex;align-items:center;gap:10px;width:100%;background:none;border:0;border-top:1px solid var(--ln);padding:8px 0;text-align:left}.lk:hover .w{color:var(--p)}.lk .w{flex:1}
.dotp{cursor:pointer;transition:r .15s}.dotp:hover{r:10}
.guide{max-width:980px}
.hero2{background:linear-gradient(160deg,#0b1d4a,#1e3a8a 70%,#1b5fa3);color:#fff;border:0;padding:28px}.hero2 h1{font-size:32px;margin-bottom:8px}.hero2 p{color:#c7d6f5;max-width:62ch;margin-bottom:16px}.hero2 .btn{background:#fff;color:#1e3a8a}
.gh{font:700 22px "Source Serif 4",serif;margin:30px 0 12px}
.flow{display:grid;grid-template-columns:repeat(6,1fr);gap:12px}
.fs{position:relative;background:var(--card);border:1px solid var(--ln);border-radius:12px;padding:14px}.fs b.n{display:grid;place-items:center;width:26px;height:26px;border-radius:50%;background:var(--p2);color:#fff;font-size:12px;margin-bottom:8px}.fs small{color:var(--mut);display:block;margin-top:2px}
.fs:not(:last-child):after{content:"→";position:absolute;right:-13px;top:42%;color:var(--p2);font-weight:700;z-index:1}
.two{display:grid;grid-template-columns:1fr 1fr;gap:16px}
.faq details{border-top:1px solid var(--ln);padding:11px 0}.faq summary{cursor:pointer;font-weight:600}.faq p{color:var(--mut);margin-top:6px}
.gl{padding-left:18px}.gl li{margin-bottom:7px}
#pubGuide{position:fixed;inset:0;background:var(--bg);z-index:40;overflow:auto}
.pubtop{display:flex;justify-content:space-between;align-items:center;padding:12px 24px;background:var(--card);border-bottom:1px solid var(--ln);position:sticky;top:0;z-index:2}
.pubin{padding:24px;max-width:1020px;margin:0 auto}
#tour{position:fixed;inset:0;z-index:50}
.spot{position:fixed;border-radius:10px;box-shadow:0 0 0 9999px rgba(8,15,35,.6),0 0 0 3px var(--p2);transition:all .3s}
.spot0{position:fixed;inset:0;background:rgba(8,15,35,.6)}
.pop{position:fixed;width:min(320px,calc(100vw - 24px));background:var(--card);border:1px solid var(--ln);border-radius:14px;padding:18px;box-shadow:0 20px 50px rgba(0,0,0,.35);animation:rise .3s both}
.pop small{color:var(--mut)}.pop h3{font-size:19px;margin:4px 0}.pop p{color:var(--mut);margin-bottom:14px}.tr{display:flex;justify-content:space-between;align-items:center}
@media(max-width:860px){.flow{grid-template-columns:1fr 1fr}.fs:after{display:none!important}.two{grid-template-columns:1fr}}
.p.stale{background:transparent;color:var(--mut);border:1px dashed var(--mut)}
#drawer.wide{width:min(660px,100%)}
.imt{width:100%;min-height:110px;font-family:ui-monospace,Menlo,monospace;font-size:12px}
.impt{width:100%;font-size:12.5px;border-collapse:collapse}.impt td,.impt th{padding:6px 8px;border-bottom:1px solid var(--ln);text-align:left;background:none}
.impt tr.bad td{background:var(--highb)}




@keyframes rise{from{opacity:0;transform:translateY(12px)}to{opacity:1;transform:none}}
@keyframes grow{from{transform:scaleX(0)}to{transform:scaleX(1)}}
@keyframes draw{to{stroke-dashoffset:0}}
@keyframes drift{to{transform:translate(-60px,50px) scale(1.15)}}
@media(max-width:860px){
#auth{grid-template-columns:1fr}.pnl{padding:26px}
#app{grid-template-columns:1fr}aside{display:none}.page{padding:18px 14px 90px}.top{padding:10px 14px}.me span{display:none}
.grid>*{grid-column:span 12!important}
.tabbar{display:flex;position:fixed;bottom:0;left:0;right:0;background:var(--card);border-top:1px solid var(--ln);padding:4px 4px calc(4px + env(safe-area-inset-bottom,0px));z-index:10}
.tabbar .nv{flex-direction:column;gap:1px;font-size:11px;padding:6px 2px;justify-content:center;text-align:center;box-shadow:none!important}}
@media(prefers-reduced-motion:reduce){*,*:before{animation:none!important;transition:none!important}.dl,.pnl svg *{stroke-dashoffset:0!important}}
.cal{display:grid;grid-template-columns:repeat(7,1fr);gap:6px}.cal .h{font-size:12px;color:var(--mut);text-align:center}.cal .d{min-height:88px;border:1px solid var(--ln);border-radius:8px;padding:6px;font-size:12px;background:var(--card);min-width:0}.cal .d.t{border-color:var(--p2);box-shadow:0 0 0 2px var(--pb)}.cal .d b{display:block;margin-bottom:3px;color:var(--mut)}.cal a{display:block;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;border-radius:5px;padding:1px 5px;margin-bottom:2px;text-decoration:none;font-size:11.5px}.cal a.od{background:var(--highb);color:var(--high)}.cal a.pl{background:var(--medb);color:var(--med)}.cal a.ip{background:var(--pb);color:var(--p)}.cal a.dn{background:var(--lowb);color:var(--low)}
@media(max-width:700px){.cal .d{min-height:54px;padding:3px;font-size:10px}.cal a{font-size:9.5px;padding:0 3px}}
.sk{background:linear-gradient(90deg,var(--ln) 25%,var(--pb) 50%,var(--ln) 75%);background-size:200% 100%;animation:shim 1.2s linear infinite;border-radius:10px}.sk-h{height:34px;width:40%;margin:6px 0 20px}.sk-r{display:grid;grid-template-columns:repeat(4,1fr);gap:16px;margin-bottom:16px}.sk-r i{height:92px}.sk-b{height:280px}@keyframes shim{to{background-position:-200% 0}}
.ban{display:flex;justify-content:space-between;align-items:flex-end;gap:16px;flex-wrap:wrap;padding:24px 26px;border-radius:16px;color:#fff;margin-bottom:20px;background:radial-gradient(520px 220px at 92% -30%,rgba(96,165,250,.55),transparent 70%),linear-gradient(135deg,#0b1d4a,#1e3a8a 70%,#1b5fa3);box-shadow:0 10px 30px rgba(30,58,138,.25)}.ban h1{font-size:30px;margin:2px 0 4px}.ban p{color:#c7d6f5}.ban small{color:#a9c1f0}.ban .btn{background:#fff;color:#1e3a8a}
.bulk{display:flex;align-items:center;gap:10px;flex-wrap:wrap;background:var(--pb);border:1px solid var(--p2);border-radius:10px;padding:10px 14px;margin-bottom:12px}.bulk[hidden]{display:none}
th.ck,td.ck{width:34px;padding-right:0}.rowck,#allck{width:16px;height:16px;accent-color:var(--p2)}
.chipsrow{display:flex;gap:8px;flex-wrap:wrap;margin-top:18px}.chipsrow span{border:1px solid rgba(255,255,255,.35);border-radius:99px;padding:4px 12px;font-size:12.5px;color:#e6efff;background:rgba(255,255,255,.08)}
.kpi .k{font-variant-numeric:tabular-nums}
.btn:focus-visible,.chip:focus-visible,.nv:focus-visible{outline:3px solid var(--p2);outline-offset:2px}
@media(max-width:860px){.sk-r{grid-template-columns:1fr 1fr}.ban{padding:18px}.ban h1{font-size:24px}}
/*HERO*/
</style>
</head>
<body>
<section id="auth">
  <div class="pnl">
    <div class="orb"></div>
    <svg viewBox="0 0 420 300" fill="none" stroke="#9db7ee" stroke-width="1.5" aria-hidden="true"><path pathLength="1" d="M20 280h380"/><path pathLength="1" d="M40 280V125M100 280V125M160 280V125"/><path pathLength="1" d="M260 280V125M320 280V125M380 280V125"/><path pathLength="1" d="M20 125h380"/><path pathLength="1" d="M40 125 210 40l170 85"/><path pathLength="1" d="M198 280v-76a12 12 0 0 1 24 0v76"/><circle pathLength="1" cx="210" cy="86" r="14"/></svg>
    <div class="logo"><svg width="30" height="30" viewBox="0 0 32 32" aria-hidden="true" style="position:static;width:30px;stroke:none;animation:none"><path d="M16 2 28 7v9c0 7-5 12-12 14C9 28 4 23 4 16V7z" fill="#fff" style="stroke-dashoffset:0;animation:none"/><path d="M16 9v8m0 4v.5" stroke="#1e3a8a" stroke-width="3" stroke-linecap="round" style="stroke-dashoffset:0;animation:none"/></svg>DropoutAlert</div>
    <div><h1>Detect early. Support better.</h1><p>Help every student succeed. DropoutAlert shows staff which students may need support, and why, so people can step in while it still matters.</p><div class="chipsrow"><span>Explainable scores</span><span>Human review first</span><span>Role-based access</span></div></div>
  </div>
  <div class="fm">
    <div id="loginV">
      <h2>Welcome back</h2><p class="sub">Sign in to your DropoutAlert account.</p>
      <label for="em">Email</label><input class="field" id="em" type="email" autocomplete="username">
      <label for="pw">Password</label><div class="pw"><input class="field" id="pw" type="password" autocomplete="current-password"><button type="button" id="eye" aria-label="Show password">Show</button></div>
      <div class="row"><label><input type="checkbox"> Remember me</label><button class="link" id="toForgot" type="button">Forgot password?</button></div>
      <button class="btn" id="signin">Sign in</button>
      <div class="msg err hide" id="err" role="alert"></div>
      <div class="demo"><b>Connected to the DropoutAlert server.</b> Sign in with the account your administrator gave you. New accounts must be approved by an administrator first.</div>
      <p style="margin-top:18px;font-size:13.5px">New here? <button class="link" id="toReg">Create an account</button></p>
    </div>
    <div id="regV" class="hide">
      <h2>Create account</h2><p class="sub">Staff accounts are reviewed before use.</p>
      <label for="rn">Full name</label><input class="field" id="rn">
      <label for="re">Email</label><input class="field" id="re" type="email">
      <label for="rr">Role</label><select class="field" id="rr"><option>Faculty</option><option>Student support</option></select>
      <label for="rp">Password</label><input class="field" id="rp" type="password" placeholder="At least 8 characters">
      <div class="msg err hide" id="rerr" role="alert"></div><div class="msg ok hide" id="rok" role="status"></div>
      <button class="btn" id="regBtn" style="margin-top:18px">Create account</button>
      <p style="margin-top:12px;font-size:12.5px;color:var(--mut)">Administrator access is granted only by an existing administrator.</p>
      <p style="margin-top:14px;font-size:13.5px"><button class="link" data-back>Back to sign in</button></p>
    </div>
    <div id="resV" class="hide">
      <h2>Choose a new password</h2><p class="sub">Use at least 8 characters, including a letter and a number.</p>
      <label for="rnp">New password</label><input class="field" id="rnp" type="password" autocomplete="new-password">
      <div class="msg err hide" id="reserr" role="alert"></div>
      <button class="btn" id="resBtn" style="margin-top:18px">Update password</button>
      <p style="margin-top:14px;font-size:13.5px"><button class="link" data-back>Back to sign in</button></p>
    </div>
    <div id="forV" class="hide">
      <h2>Reset password</h2><p class="sub">Enter your email and we will send a single-use link if the account exists.</p>
      <label for="fe">Email</label><input class="field" id="fe" type="email">
      <div class="msg ok hide" id="fok" role="status"></div>
      <button class="btn" id="forBtn" style="margin-top:18px">Send reset link</button>
      <p style="margin-top:14px;font-size:13.5px"><button class="link" data-back>Back to sign in</button></p>
    </div>
  </div>
</section>

<section id="app" class="hide">
  <aside id="side"></aside>
  <main>
    <header class="top">
      <div class="sr"><svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><circle cx="11" cy="11" r="7"/><path d="m20 20-4-4"/></svg><input class="field" id="q" placeholder="Search students" aria-label="Search students"></div>
      <div class="me"><button class="ib" id="theme" aria-label="Switch theme">◐</button><div class="av">AD</div><span style="font-weight:600">Admin</span><button class="btn s" id="out" style="padding:7px 12px">Log out</button></div>
    </header>
    <div class="page" id="page"></div>
  </main>
  <nav class="tabbar" id="tabs" aria-label="Main"></nav>
</section>
<aside id="drawer" aria-label="Student risk details"></aside>
<div id="toast" class="hide" role="status"></div>

<script src="/static/app.js"></script>
</body>
</html>
'''

APP_JS = r'''const $=s=>document.querySelector(s),$$=s=>[...document.querySelectorAll(s)];
const esc=s=>String(s??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
let ME=null,UNREAD=0,rid=0,PT='ov',SF={q:'',course:'',category:'',sort:'name',order:'asc',page:1},IF={status:'',priority:''};
const LB={high:'High risk',medium:'Medium risk',low:'Low risk',incomplete:'Data incomplete'},SH={high:'▲',medium:'◆',low:'●',incomplete:'○'};
const pill=c=>c?`<span class="p ${c==='incomplete'?'stale':c}"><span aria-hidden="true">${SH[c]}</span>${LB[c]}</span>`:'';
const ini=n=>String(n||'?').split(' ').map(p=>p[0]).join('').slice(0,2).toUpperCase();
const pc=v=>v==null?'<span class="p stale">Missing</span>':v+'%';
const dd=d=>Math.round((new Date(d+'T00:00:00')-new Date().setHours(0,0,0,0))/864e5);
const emsg=e=>e.message+(e.details&&Object.keys(e.details).length?' ('+Object.entries(e.details).map(([k,v])=>k+': '+v).join('; ')+')':'');
const ICON={dash:'<path d="M3 12 12 4l9 8M5 10v10h14V10"/>',students:'<circle cx="9" cy="8" r="3.5"/><path d="M2.5 20c.6-4 3-6 6.5-6s5.9 2 6.5 6M16 5a3.5 3.5 0 0 1 0 7M18 14c2 .6 3.2 2.4 3.5 6"/>',interventions:'<path d="M4 6h16M4 12h16M4 18h10"/>',alerts:'<path d="M6 16V11a6 6 0 0 1 12 0v5l2 2H4l2-2zM10 21h4"/>',rules:'<path d="M12 3 3 20h18L12 3zM12 10v4M12 17v.5"/>',settings:'<circle cx="12" cy="12" r="3"/><path d="M12 2v3M12 19v3M2 12h3M19 12h3M5 5l2 2M17 17l2 2M19 5l-2 2M7 17l-2 2"/>',guide:'<circle cx="12" cy="12" r="9"/><path d="M9.5 9.5a2.5 2.5 0 1 1 3.5 2.3c-.7.4-1 .9-1 1.7M12 17v.5"/>'};
const ic=k=>`<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">${ICON[k]}</svg>`;
function toast(t){const e=$('#toast');e.textContent=t;e.classList.remove('hide');clearTimeout(toast.t);toast.t=setTimeout(()=>e.classList.add('hide'),3200)}
async function api(method,url,body){const o={method,headers:{'X-Requested-With':'DropoutAlert'},credentials:'same-origin'};if(body!==undefined){o.headers['Content-Type']='application/json';o.body=JSON.stringify(body)}
 const r=await fetch('/api'+url,o);let d=null;try{d=await r.json()}catch(e){}if(!r.ok){const er=(d&&d.error)||{},e=new Error(er.message||'Request failed ('+r.status+')');e.status=r.status;e.details=er.details||{};throw e}return d}
// theme
const setTheme=t=>{document.documentElement.dataset.theme=t;try{localStorage.setItem('da-theme',t)}catch(e){}};
try{const t=localStorage.getItem('da-theme');if(t)document.documentElement.dataset.theme=t}catch(e){}
$('#theme').onclick=()=>setTheme(document.documentElement.dataset.theme==='dark'?'light':'dark');
// auth views
const views=['loginV','regV','forV','resV'],showV=id=>views.forEach(v=>$('#'+v).classList.toggle('hide',v!==id)),msg=(id,t)=>{const e=$(id);e.textContent=t;e.classList.remove('hide')};
$('#toReg').onclick=()=>showV('regV');$('#toForgot').onclick=()=>showV('forV');$$('[data-back]').forEach(b=>b.onclick=()=>showV('loginV'));
$('#eye').onclick=()=>{const p=$('#pw'),s=p.type==='password';p.type=s?'text':'password';$('#eye').textContent=s?'Hide':'Show'};
$('#signin').onclick=async()=>{try{ME=(await api('POST','/auth/login',{email:$('#em').value.trim(),password:$('#pw').value})).user;$('#err').classList.add('hide');enter()}catch(e){msg('#err',emsg(e))}};
$('#pw').addEventListener('keydown',e=>{if(e.key==='Enter')$('#signin').click()});
$('#regBtn').onclick=async()=>{['#rerr','#rok'].forEach(i=>$(i).classList.add('hide'));try{const d=await api('POST','/auth/register',{name:$('#rn').value.trim(),email:$('#re').value.trim(),password:$('#rp').value,role:$('#rr').value==='Faculty'?'faculty':'support'});msg('#rok',d.message)}catch(e){msg('#rerr',emsg(e))}};
$('#forBtn').onclick=async()=>{try{msg('#fok',(await api('POST','/auth/forgot',{email:$('#fe').value.trim()})).message)}catch(e){msg('#fok',emsg(e))}};
$('#resBtn').onclick=async()=>{try{await api('POST','/auth/reset',{token:new URLSearchParams(location.search).get('token'),password:$('#rnp').value});history.replaceState(null,'',location.pathname);showV('loginV');toast('Password updated. Sign in with the new one.')}catch(e){msg('#reserr',emsg(e))}};
$('#out').onclick=async()=>{try{await api('POST','/auth/logout')}catch(e){}ME=null;SEL.clear();closeD();location.hash='';$('#app').classList.add('hide');$('#auth').classList.remove('hide');showV('loginV')};
async function boot(){if(new URLSearchParams(location.search).get('token'))showV('resV');try{ME=(await api('GET','/auth/me')).user;enter()}catch(e){}}
function enter(){$('#auth').classList.add('hide');$('#app').classList.remove('hide');$('.me .av').textContent=ini(ME.name);$('.me span').textContent=ME.name;if(!location.hash||location.hash==='#')location.hash=ME.role==='student'?'#/mine':'#/dash';$('.sr').style.display=ME.role==='student'?'none':'';render();tourHint()}
// shell and routing
const route=()=>{const h=location.hash.replace(/^#\/?/,'').split('/');return{k:h[0]||'dash',id:h[1]}};
const NAVS=()=>ME.role==='student'?[['mine','My progress'],['settings','Settings']]:[['dash','Dashboard'],['students','Students'],['interventions','Interventions'],['analytics','Analytics'],['alerts','Alerts'],...(ME.role==='admin'?[['rules','Risk rules']]:[]),['settings','Settings'],['guide','Guide']];
function shell(k){const n=NAVS().map(([a,l])=>`<button class="nv" data-href="#/${a}" ${a===k?'aria-current="page"':''}>${ic(a)}${l}${a==='alerts'&&UNREAD?`<span class="bdg">${UNREAD}</span>`:''}</button>`).join('');
 $('#side').innerHTML=`<div class="logo" style="color:var(--p)"><svg width="28" height="28" viewBox="0 0 32 32" aria-hidden="true"><path d="M16 2 28 7v9c0 7-5 12-12 14C9 28 4 23 4 16V7z" fill="var(--p)"/><path d="M16 9v8m0 4v.5" stroke="var(--card)" stroke-width="3" stroke-linecap="round"/></svg>DropoutAlert</div>${n}<div class="foot">Connected to the server. Scores are indicators for human review.</div>`;
 $('#tabs').innerHTML=NAVS().filter(x=>ME.role==='student'||['dash','students','interventions','alerts','guide'].includes(x[0])).map(([a,l])=>`<button class="nv" data-href="#/${a}" ${a===k?'aria-current="page"':''}>${ic(a)}${l}</button>`).join('')}
const V={};
async function render(){if(!ME)return;const r=route(),my=++rid,pg=$('#page');if(ME.role==='student'&&!['mine','settings'].includes(r.k)){location.hash='#/mine';return}shell(r.k);pg.innerHTML=skel();
 try{const f=V[r.k];if(!f){pg.innerHTML='<div class="ph2"><div><h2>Page not found</h2><button class="btn" data-href="#/dash">Back to dashboard</button></div></div>';return}
  const html=await f(r);if(my!==rid)return;pg.innerHTML=html;pg.classList.remove('rise');void pg.offsetWidth;pg.classList.add('rise');countUp();document.title='DropoutAlert – '+((NAVS().find(n=>n[0]===r.k)||[0,'Student Dropout Early Warning'])[1])}
 catch(e){if(my!==rid)return;if(e.status===401){ME=null;$('#app').classList.add('hide');$('#auth').classList.remove('hide');toast('Your session ended. Please sign in again.');return}pg.innerHTML=`<div class="msg err" role="alert">${esc(emsg(e))}</div><p style="margin-top:12px"><button class="btn s" data-href="#/dash">Back to dashboard</button></p>`}
 refreshBell()}
async function refreshBell(){if(ME&&ME.role==='student')return;try{const d=await api('GET','/notifications?unread=1');if(d.unread!==UNREAD){UNREAD=d.unread;const b=$$('#side [data-href="#/alerts"]')[0];if(b){b.querySelector('.bdg')?.remove();if(UNREAD)b.insertAdjacentHTML('beforeend',`<span class="bdg">${UNREAD}</span>`)}}}catch(e){}}
addEventListener('hashchange',render);
const kpi=(i,n,l,col)=>`<div class="card kpi c3 rise" style="--i:${i};--a:${col}"><span class="k">${n}</span><span class="l">${l}</span></div>`;
const head=(h,l,act='')=>`<div class="ph"><div><h1>${h}</h1><p class="lead">${l}</p></div>${act}</div>`;
const srow=(s,ck)=>`<tr class="rd" tabindex="0" data-href="#/students/${s.id}">${ck?`<td class="ck"><input type="checkbox" class="rowck" data-id="${s.id}" ${SEL.has(s.id)?'checked':''} aria-label="Select ${esc(s.name)}"></td>`:''}<td><div class="nm"><span class="av">${ini(s.name)}</span><span><b>${esc(s.name)}</b><br><small style="color:var(--mut)">${esc(s.code)}${s.outdated?' <span class="p stale">Outdated data</span>':''}</small></span></div></td><td>${esc(s.course)}</td><td>${pc(s.attendance)}</td><td>${pc(s.marks)}</td><td><b>${s.risk.score??'-'}</b></td><td>${pill(s.risk.category)}</td></tr>`;
const ivStat=i=>i.overdue?'<span class="p high">Overdue</span>':`<span class="p ${{planned:'medium',in_progress:'t',completed:'low',cancelled:'stale'}[i.status]}">${i.status.replace('_',' ')}</span>`;
const dlab=i=>{if(['completed','cancelled'].includes(i.status))return 'Done';const d=dd(i.due_date);return d<0?`${-d} day${d<-1?'s':''} overdue`:d===0?'Today':d===1?'Tomorrow':i.due_date};
// dashboard
V.dash=async()=>{const [sm,st,iv]=await Promise.all([api('GET','/reports/summary'),api('GET','/students?sort=risk_score&order=desc&per_page=100'),api('GET','/interventions')]);
 const c=k=>sm.by_category[k]||0,all=st.students,attn=all.filter(s=>['high','medium','incomplete'].includes(s.risk.category)),act=iv.interventions.filter(i=>['planned','in_progress'].includes(i.status)),od=act.filter(i=>i.overdue),wk=act.filter(i=>!i.overdue&&dd(i.due_date)<=7),mine=act.filter(i=>i.assignee_id===ME.id),hr=new Date().getHours(),gr=hr<12?'Good morning':hr<17?'Good afternoon':'Good evening';
 const wl=i=>`<div class="wl"><span class="w"><a href="#/students/${i.student_id}" class="link">${esc(i.student_name)}</a><small>${esc(i.category)}, ${dlab(i)}, ${esc(i.assignee_name)}</small></span>${ivStat(i)}</div>`;
 const tbl=(t,n,rows)=>`<div class="card flush c8 rise" style="--i:5"><div class="hd"><div><h2>${t}</h2><p class="nt" style="margin:0">${n}</p></div></div><div class="tw"><table><tr><th>Student</th><th>Course</th><th>Attendance</th><th>Marks</th><th>Score</th><th>Risk</th></tr>${rows.length?rows.map(s=>srow(s)).join(''):'<tr><td colspan="6" class="empty">Nothing needs attention right now.</td></tr>'}</table></div></div>`;
 let h,b;
 if(ME.role==='support'){const nc=all.filter(s=>s.risk.category==='high'&&!act.some(i=>i.student_id===s.id));
  h=kpi(1,act.length,'Active interventions','var(--p2)')+kpi(2,od.length,'Overdue','var(--high)')+kpi(3,wk.length,'Due in the next 7 days','var(--med)')+kpi(4,nc.length,'High risk with no active support','var(--high)');
  b=[['Overdue',od],['This week',wk]].map(([t,L])=>`<div class="card c4 rise" style="--i:6"><h2>${t} <span class="p t">${L.length}</span></h2><p class="nt">&nbsp;</p>${L.length?L.map(wl).join(''):'<p class="empty">Nothing here.</p>'}</div>`).join('')+`<div class="card c4 rise" style="--i:6"><h2>New concerns</h2><p class="nt">High risk and no active support</p>${nc.length?nc.map(s=>`<div class="wl"><span class="w"><a class="link" href="#/students/${s.id}">${esc(s.name)}</a><small>Score ${s.risk.score}</small></span><button class="btn s" style="padding:4px 10px" data-newiv="${s.id}">Start support</button></div>`).join(''):'<p class="empty">Everyone high-risk has support.</p>'}</div>`}
 else{h=kpi(1,sm.students,ME.role==='faculty'?'My students':'Enrolled students','var(--p2)')+kpi(2,c('high'),'High risk, review now','var(--high)')+kpi(3,c('medium'),'Medium risk, monitor','var(--med)')+kpi(4,c('low')+c('incomplete'),`Low risk${c('incomplete')?` (${c('incomplete')} with incomplete data)`:''}`,'var(--low)');
  const tot=sm.students||1,side=ME.role==='admin'?`<div class="card c4 rise" style="--i:6"><h2>Risk distribution</h2><p class="nt">Every student in your view</p><div class="stk">${[['high','#b91c1c'],['medium','#d97706'],['low','#16a34a'],['incomplete','#94a3b8']].map(([k,col])=>`<i style="flex:${c(k)||.001};background:${col}"></i>`).join('')}</div>${['high','medium','low','incomplete'].map(k=>`<div class="lg">${pill(k)}<span class="w"></span><b>${c(k)}</b></div>`).join('')}</div>`:`<div class="card c4 rise" style="--i:6"><h2>My follow-ups</h2><p class="nt">Soonest first</p>${mine.length?mine.map(wl).join(''):'<p class="empty">Nothing assigned to you.</p>'}</div>`;
  b=tbl('Students who may need attention','Sorted by score. Select a row to see why.',attn.slice(0,8))+side+(ME.role==='admin'?`<div class="card c6 rise" style="--i:7"><h2>Average score by course</h2><p class="nt">Select a course to open its students</p>${sm.by_course.map(x=>`<a class="lk" style="text-decoration:none" href="#/students" data-course="${esc(x.course)}"><div style="display:flex;justify-content:space-between;width:100%"><span>${esc(x.course)}</span><b>${x.average_score}</b></div></a>`).join('')}</div><div class="card c6 rise" style="--i:8"><h2>Contributing factors</h2><p class="nt">Students with points from each factor</p>${Object.entries(sm.factors).map(([k,v])=>`<div class="fac"><div class="t"><span>${esc(k)}</span><b>${v} of ${tot}</b></div><div class="trk"><i style="width:${v/tot*100}%"></i></div></div>`).join('')||'<p class="empty">No factors yet.</p>'}</div>`:'')}
 return banner(gr,ME.role==='admin'?pdfBtn:'<button class="btn" data-newiv="">New intervention</button>')+`<div class="grid">${h}${b}</div><p class="note">Risk scores are illustrative indicators for human review. They are not predictions, and they never trigger automatic action.</p>`};
// students
V.students=async r=>{if(r.id)return profile(r.id);
 const p=new URLSearchParams({sort:SF.sort,order:SF.order,page:SF.page,per_page:10});['q','course','category'].forEach(k=>SF[k]&&p.set(k,SF[k]));
 const [d,sm,sv]=await Promise.all([api('GET','/students?'+p),api('GET','/reports/summary'),api('GET','/views')]),th=(k,l)=>`<th><button class="sort" data-sort="${k}">${l}${SF.sort===k?(SF.order==='asc'?' ↑':' ↓'):''}</button></th>`,can=['admin','faculty'].includes(ME.role);
 return head('Student directory',`${d.total} student${d.total===1?'':'s'} you can see. Search with the top bar.`,`<div style="display:flex;gap:8px;flex-wrap:wrap">${ME.role==='admin'?'<button class="btn s" data-imp>Import CSV</button>':''}<a class="btn s" href="/api/students/export.csv" style="text-decoration:none">Export CSV</a>${can?'<button class="btn" data-add>Add student</button>':''}</div>`)+
 `<div class="fl"><select class="field sel" id="fc" aria-label="Course"><option value="">All courses</option>${sm.by_course.map(c=>`<option ${SF.course===c.course?'selected':''}>${esc(c.course)}</option>`).join('')}</select><select class="field sel" id="fr" aria-label="Risk category"><option value="">All risk levels</option>${Object.keys(LB).map(k=>`<option value="${k}" ${SF.category===k?'selected':''}>${LB[k]}</option>`).join('')}</select>${viewsCtl(sv.views)}</div>
 ${bulkBar()}<div class="card flush"><div class="tw"><table><tr><th class="ck"><input type="checkbox" id="allck" aria-label="Select all on this page"></th>${th('name','Student')}${th('course','Course')}${th('attendance','Attendance')}${th('marks','Marks')}${th('risk_score','Score')}<th>Risk</th></tr>${d.students.length?d.students.map(s=>srow(s,1)).join(''):'<tr><td colspan="7" class="empty">No students match. Clear the search or change a filter.</td></tr>'}</table></div><div class="pgn"><span>Page ${d.page} of ${d.pages||1}</span><span><button class="btn s" data-page="-1" style="padding:5px 12px" ${d.page>1?'':'disabled'}>Previous</button> <button class="btn s" data-page="1" style="padding:5px 12px" ${d.page<d.pages?'':'disabled'}>Next</button></span></div></div>`};
const REASON={created:'Added',data_updated:'Records updated',rules_changed:'Scoring rules changed',imported:'Imported from CSV',profile_edited:'Profile edited',seed:'Demo data'};
const ACT={Attendance:'Speak with the student about what is getting in the way of attending.',Marks:'Offer tutoring or a study plan for the weakest subjects.','Assignment completion':'Check workload and offer help with submission deadlines.'};
async function profile(id){const [a,h,iv,at]=await Promise.all([api('GET','/students/'+id),api('GET','/students/'+id+'/assessments'),api('GET','/interventions'),api('GET','/students/'+id+'/attendance')]),s=a.student,rk=s.risk,mine=iv.interventions.filter(i=>i.student_id===s.id),can=['admin','faculty'].includes(ME.role);
 if(PT==='upd'&&!can)PT='ov';let b;
 if(PT==='ov')b=`<div class="grid"><div class="card c4"><h2>Risk score</h2><p class="nt">Assessed ${rk.assessed_at?rk.assessed_at.slice(0,16).replace('T',' ')+' UTC':'never'}</p><div style="display:flex;align-items:flex-end;gap:12px;margin-bottom:8px"><span class="big">${rk.score??'-'}</span>${pill(rk.category)}</div>${rk.factors.map(f=>`<div class="fac"><div class="t"><span>${esc(f.factor)} <small style="color:var(--mut)">${f.value==null?'missing':'at '+f.value+'%'}</small></span><b>${f.points==null?'No data':f.points?'+'+f.points+' points':'No points'}</b></div><div class="trk"><i style="width:${(f.points||0)*2.5}%;background:${f.points?'var(--high)':'var(--low)'}"></i></div></div>`).join('')}</div>
 <div class="card c8"><h2>Score history</h2><p class="nt">Every recalculation is kept</p>${h.assessments.map((x,i,r)=>{const p=r[i+1],d=p?x.score-p.score:0;return `<div class="lg"><span class="w"><b>${REASON[x.reason]||esc(x.reason)}</b><br><small style="color:var(--mut)">${x.created_at.slice(0,16).replace('T',' ')}${d?`, ${d>0?'up':'down'} ${Math.abs(d)} points`:''}</small></span>${pill(x.category)}<b style="width:34px;text-align:right">${x.score}</b></div>`}).join('')}</div>
 <div class="card c12"><h2>Suggested review actions</h2><p class="nt">Starting points for a human conversation</p><ul style="padding-left:18px">${rk.factors.filter(f=>f.points).map(f=>`<li style="margin-bottom:5px">${ACT[f.factor]}</li>`).join('')||'<li>No action suggested. Keep monitoring.</li>'}${rk.missing.length?`<li>Fill in the missing data: ${rk.missing.map(esc).join(', ')}.</li>`:''}</ul></div></div>`;
 else if(PT==='att')b=attTab(s,at.attendance,can);
 else if(PT==='iv')b=`<div class="card"><div style="display:flex;justify-content:space-between;align-items:center"><div><h2>Interventions</h2><p class="nt">Support recorded for ${esc(s.name)}</p></div><button class="btn" data-newiv="${s.id}">New intervention</button></div>${mine.length?mine.map(i=>`<div class="lg"><span class="w"><b>${esc(i.category)}</b>, ${esc(i.priority)} priority<br><small style="color:var(--mut)">${esc(i.description)} Assigned to ${esc(i.assignee_name)}, ${dlab(i)}.${i.outcome?' Outcome: '+esc(i.outcome.replace('_',' '))+'.':''}</small></span>${ivStat(i)}</div>`).join(''):'<p class="empty">No interventions yet.</p>'}</div>`;
 else b=`<div class="card" style="max-width:520px"><h2>Update records</h2><p class="nt">Leave a field empty if the value is unknown. It will be shown as missing, never as good performance.</p>${[['uA','Attendance %',s.attendance],['uM','Marks %',s.marks],['uG','Assignment completion %',s.assignments]].map(([i,l,v])=>`<label for="${i}">${l}</label><input class="field" id="${i}" type="number" min="0" max="100" value="${v??''}">`).join('')}<div class="msg err hide" id="uerr" role="alert"></div><button class="btn" id="updSave" data-id="${s.id}" style="margin-top:16px">Save and recalculate</button></div>`;
 return `<a class="back" href="#/students" style="text-decoration:none;display:inline-block">← All students</a>${head(esc(s.name),`${esc(s.code)}, ${esc(s.course)}`,`<div style="display:flex;gap:10px;align-items:center;flex-wrap:wrap">${pill(rk.category)}${s.outdated?' <span class="p stale">Outdated data</span>':''}<a class="btn s" href="/api/students/${s.id}/report.pdf" style="text-decoration:none">Download PDF</a></div>`)}${s.outdated?`<div class="msg err" style="margin-bottom:14px">This record has not been updated recently. Confirm the figures before acting on the score.</div>`:''}<div class="tabs" role="group" aria-label="Profile sections">${[['ov','Overview'],['att','Attendance'],['iv','Interventions'],...(can?[['upd','Update records']]:[])].map(([k,l])=>`<button data-pt="${k}" aria-pressed="${PT===k}">${l}</button>`).join('')}</div>${b}<p class="note">An indicator for review, not a prediction. Check the data and the student’s context before acting.</p>`}
// interventions
V.interventionsList=async()=>{const p=new URLSearchParams();IF.status&&p.set('status',IF.status);IF.priority&&p.set('priority',IF.priority);const d=await api('GET','/interventions?'+p);
 const ac=i=>{const own=ME.role!=='faculty'||i.assignee_id===ME.id;if(!own)return'';return i.status==='planned'?`<button class="btn s" style="padding:4px 10px" data-ivs="${i.id}:in_progress">Start</button> <button class="btn s" style="padding:4px 10px" data-ivs="${i.id}:cancelled">Cancel</button>`:i.status==='in_progress'?`<button class="btn s" style="padding:4px 10px" data-done="${i.id}">Complete</button> <button class="btn s" style="padding:4px 10px" data-ivs="${i.id}:cancelled">Cancel</button>`:`<small style="color:var(--mut)">${esc((i.outcome||'').replace('_',' '))}</small>`};
 const op=(a,v)=>a.map(x=>`<option value="${x}" ${v===x?'selected':''}>${x.replace('_',' ')}</option>`).join('');
 return head('Interventions','Support actions, follow-ups and outcomes.','<button class="btn" data-newiv="">New intervention</button>')+`<div class="fl"><select class="field sel" id="fis" aria-label="Status"><option value="">All statuses</option>${op(['planned','in_progress','completed','cancelled'],IF.status)}</select><select class="field sel" id="fip" aria-label="Priority"><option value="">All priorities</option>${op(['high','medium','low'],IF.priority)}</select></div><div class="card flush"><div class="tw"><table><tr><th>Student</th><th>Support</th><th>Priority</th><th>Assigned to</th><th>Follow-up</th><th>Status</th><th></th></tr>${d.interventions.length?d.interventions.map(i=>`<tr><td><a class="link" href="#/students/${i.student_id}">${esc(i.student_name)}</a></td><td>${esc(i.category)}</td><td>${esc(i.priority)}</td><td>${esc(i.assignee_name)}</td><td style="${i.overdue?'color:var(--high);font-weight:600':''}">${dlab(i)}</td><td>${ivStat(i)}</td><td>${ac(i)}</td></tr>`).join(''):'<tr><td colspan="7" class="empty">No interventions match these filters.</td></tr>'}</table></div></div>`};
// alerts
V.alerts=async()=>{const d=await api('GET','/notifications');UNREAD=d.unread;return head('Alerts','Created by real changes: risk rises, new assignments, overdue follow-ups and completed support.','<button class="btn s" data-readall>Mark all read</button>')+`<div class="card flush">${d.notifications.length?d.notifications.map(n=>`<button class="al" data-nid="${n.id}" data-sid="${n.student_id||''}"><span class="dot2" style="opacity:${n.read?0:1}"></span><span class="w"><b style="font-weight:${n.read?500:700}">${esc(n.title)}</b><small>${esc(n.body)}</small></span><small>${n.created_at.slice(0,16).replace('T',' ')}</small></button>`).join(''):'<p class="empty">No alerts yet.</p>'}</div>`};
// rules (admin)
const FACT=[['attendance','Attendance'],['marks','Marks'],['assignments','Assignment completion']];
V.rules=async()=>{if(ME.role!=='admin')throw Object.assign(new Error('Administrators only.'),{status:403});const R=(await api('GET','/rules')).rules;
 return head('Risk rules','The scoring rules behind every score. Saving recalculates every student.')+`<div class="card" style="max-width:700px" id="cfForm"><div class="cf"><b></b><small>Lower below</small><small>Points</small><small>Upper below</small><small>Points</small></div>${FACT.map(([f,l])=>`<div class="cf"><b>${l}</b>${[R[f][0][0],R[f][0][1],R[f][1][0],R[f][1][1]].map((v,i)=>`<input class="field" id="cf-${f}-${i}" type="number" value="${v}" aria-label="${l} value ${i+1}">`).join('')}</div>`).join('')}<div class="cf"><b>Categories</b><small>Medium from</small><input class="field" id="cf-med" type="number" value="${R.medium}"><small>High from</small><input class="field" id="cf-high" type="number" value="${R.high}"></div><div class="cf"><b>Outdated after</b><small>Days</small><input class="field" id="cf-stale" type="number" value="${R.stale_days}"></div><div class="msg err hide" id="cferr" role="alert"></div><button class="btn" id="cfSave" style="margin-top:12px">Save and recalculate</button></div><p class="note">These are illustrative demonstration rules, not validated predictions.</p>`};
// settings
V.settings=async()=>{let adm='';const pr=ME.role==='student'?{}:(await api('GET','/auth/prefs')).prefs;if(ME.role==='admin'){const [u,a,rs]=await Promise.all([api('GET','/users'),api('GET','/audit'),api('GET','/resources')]);
 adm=`${createAcctCard()}${resCard(rs.text)}<div class="card flush c12"><div class="hd"><div><h2>Accounts</h2><p class="nt" style="margin:0">Approve new registrations and set faculty course access.</p></div></div><div class="tw"><table><tr><th>Name</th><th>Role</th><th>Status</th><th>Courses (faculty)</th><th></th></tr>${u.users.map(x=>`<tr><td><b>${esc(x.name)}</b><br><small style="color:var(--mut)">${esc(x.email)}</small></td><td>${x.role}</td><td>${x.active?'<span class="p low">Active</span>':'<span class="p medium">Pending</span>'}</td><td>${x.role==='faculty'?`<input class="field" style="padding:5px 8px" id="uc${x.id}" value="${esc((x.courses||[]).join(', '))}" aria-label="Courses for ${esc(x.name)}">`:(x.student_code?'Student '+esc(x.student_code):'-')}</td><td style="white-space:nowrap">${x.id===ME.id?'':`<button class="btn s" style="padding:4px 10px" data-usr="${x.id}:${x.active?'off':'on'}">${x.active?'Deactivate':'Approve'}</button> `}${x.role==='faculty'?`<button class="btn s" style="padding:4px 10px" data-usr="${x.id}:courses">Save courses</button>`:''}</td></tr>`).join('')}</table></div></div>
 <div class="card flush c12"><div class="hd"><div><h2>Audit trail</h2><p class="nt" style="margin:0">Latest events. Passwords are never recorded.</p></div></div><div class="tw"><table><tr><th>Time (UTC)</th><th>Event</th><th>Detail</th></tr>${a.events.slice(0,15).map(e=>`<tr><td>${e.created_at.slice(0,16).replace('T',' ')}</td><td>${esc(e.action)}</td><td>${esc(e.detail)}</td></tr>`).join('')}</table></div></div>`}
 return head('Settings','Your account'+(ME.role==='admin'?', accounts and the audit trail.':'.'))+`<div class="grid"><div class="card c6"><h2>Change password</h2><p class="nt">Other sessions on your account will be signed out.</p><label for="pc">Current password</label><input class="field" id="pc" type="password" autocomplete="current-password"><label for="pn">New password</label><input class="field" id="pn" type="password" autocomplete="new-password"><div class="msg err hide" id="pe" role="alert"></div><button class="btn" id="pwSave" style="margin-top:14px">Update password</button></div>${ME.role==='student'?'':prefsCard(pr)}<div class="card c6"><h2>Account</h2><p class="nt">${esc(ME.email)}</p><label for="pnm">Display name</label><input class="field" id="pnm" value="${esc(ME.name)}" maxlength="120"><button class="btn s" id="nmSave" style="margin:10px 0 14px">Save name</button><p>Role: <b>${ROLEN[ME.role]}</b></p>${ME.role==='faculty'?`<p style="margin-top:8px">Courses: ${esc((ME.courses||[]).join(', ')||'none assigned yet')}</p>`:''}</div>${adm}</div>`};
// drawer
const closeD=()=>$('#drawer').classList.remove('open','wide');
function drawer(h,wide){$('#drawer').innerHTML=`<button class="ib" id="dclose" aria-label="Close" style="margin-left:auto">✕</button>`+h;$('#drawer').classList.toggle('wide',!!wide);$('#drawer').classList.add('open');const f=$('#drawer input,#drawer select,#drawer textarea');f&&f.focus()}
const dmsg=id=>`<div class="msg err hide" id="${id}" role="alert"></div>`;
const num=id=>{const v=$('#'+id).value.trim();return v===''?null:Number(v)};
function openAdd(){drawer(`<h2 style="font-size:24px;margin:6px 0 4px">Add student</h2><p class="nt">Leave a figure empty if unknown. It is stored as missing.</p><label for="an">Full name</label><input class="field" id="an"><label for="ac">Course</label><input class="field" id="ac" list="cl" value="${esc((ME.courses||[])[0]||'')}"><datalist id="cl">${[...new Set($$('tr.rd td:nth-child(2)').map(t=>t.textContent))].map(c=>`<option value="${esc(c)}">`).join('')}</datalist>${[['aa','Attendance %'],['am','Marks %'],['ag','Assignment completion %']].map(([i,l])=>`<label for="${i}">${l}</label><input class="field" id="${i}" type="number" min="0" max="100">`).join('')}${dmsg('aerr')}<button class="btn" id="addSave" style="margin-top:16px;width:100%">Add student</button>`)}
function openImp(){drawer(`<h2 style="font-size:24px;margin:6px 0 4px">Import students from CSV</h2><p class="nt">Columns: name, course, attendance, marks, assignments. Blank numbers are stored as missing. Nothing is imported until you review the preview.</p><label for="imf">Choose a .csv file</label><input type="file" id="imf" accept=".csv,text/csv" class="field"><label for="imt">Or paste CSV text</label><textarea class="field imt" id="imt"></textarea>${dmsg('imerr')}<button class="btn" id="imPrev" style="margin-top:14px">Preview</button><div id="imres"></div>`,true)}
function openIv(sid){Promise.all([api('GET','/students?per_page=100'),ME.role==='admin'?api('GET','/users'):Promise.resolve(null)]).then(([st,us])=>{const staff=us?us.users.filter(u=>u.active):[ME],d=new Date();d.setDate(d.getDate()+7);const dv=d.toISOString().slice(0,10);
 drawer(`<h2 style="font-size:24px;margin:6px 0 4px">New intervention</h2><p class="nt">Record the support plan. A person should review the student’s context first.</p><label for="vs">Student</label><select class="field" id="vs"><option value="">Choose a student</option>${st.students.map(s=>`<option value="${s.id}" ${String(s.id)===String(sid)?'selected':''}>${esc(s.name)}</option>`).join('')}</select><label for="vc">Category</label><select class="field" id="vc">${['Attendance','Academic','Assignments','Mentoring','Wellbeing'].map(x=>`<option>${x}</option>`).join('')}</select><label for="vp">Priority</label><select class="field" id="vp"><option>high</option><option selected>medium</option><option>low</option></select><label for="vw">Assigned to</label><select class="field" id="vw">${staff.map(u=>`<option value="${u.id}" ${u.id===ME.id?'selected':''}>${esc(u.name)}</option>`).join('')}</select><label for="vd">Follow-up date</label><input class="field" id="vd" type="date" value="${dv}"><label for="vt">Planned action</label><textarea class="field" id="vt" rows="3"></textarea>${dmsg('verr')}<button class="btn" id="ivSave" style="margin-top:16px;width:100%">Create intervention</button>`)}).catch(e=>toast(emsg(e)))}
const fail=(id,e)=>{const x=$(id);x.textContent=emsg(e);x.classList.remove('hide')};
async function act(fn){try{await fn()}catch(e){if(e.status===401){ME=null;$('#app').classList.add('hide');$('#auth').classList.remove('hide')}else toast(emsg(e))}}
document.addEventListener('click',e=>act(async()=>{const t=e.target;let b;
 if(t.closest('.ck')){}
 else if(b=t.closest('[data-href]'))location.hash=b.dataset.href;
 else if(b=t.closest('[data-course]')){SF.course=b.dataset.course;SF.page=1}
 else if(b=t.closest('[data-sort]')){const k=b.dataset.sort;SF.order=SF.sort===k&&SF.order==='asc'?'desc':'asc';SF.sort=k;SF.page=1;render()}
 else if(b=t.closest('[data-page]')){SF.page+=+b.dataset.page;render()}
 else if(b=t.closest('[data-pt]')){PT=b.dataset.pt;render()}
 else if(t.closest('#dclose'))closeD();
 else if(t.closest('[data-add]'))openAdd();
 else if(t.closest('[data-imp]'))openImp();
 else if(b=t.closest('[data-newiv]'))openIv(b.dataset.newiv);
 else if(t.closest('#addSave')){try{const r=await api('POST','/students',{name:$('#an').value.trim(),course:$('#ac').value.trim(),attendance:num('aa'),marks:num('am'),assignments:num('ag')});closeD();toast('Student added.');location.hash='#/students/'+r.student.id}catch(x){fail('#aerr',x)}}
 else if(t.closest('#imPrev')){const txt=$('#imt').value;try{const r=await api('POST','/students/import?preview=1',{csv:txt});IMP=txt;$('#imerr').classList.add('hide');$('#imres').innerHTML=`<h3 style="font-size:17px;margin:18px 0 6px">Preview</h3><p class="nt">${r.valid} valid, ${r.rejected} will be rejected.</p><div class="tw"><table class="impt"><tr><th>Line</th><th>Name</th><th>Course</th><th>Result</th></tr>${r.rows.map(x=>`<tr class="${x.ok?'':'bad'}"><td>${x.line}</td><td>${esc(x.data.name||'')}</td><td>${esc(x.data.course||'')}</td><td>${x.ok?'Ready':esc(Object.entries(x.errors).map(([k,v])=>k+': '+v).join('; '))}</td></tr>`).join('')}</table></div><button class="btn" id="imGo" style="margin-top:14px" ${r.valid?'':'disabled'}>Import ${r.valid} valid row${r.valid===1?'':'s'}</button>`}catch(x){fail('#imerr',x)}}
 else if(t.closest('#imGo')){const r=await api('POST','/students/import',{csv:IMP});closeD();toast(`Imported ${r.imported}. ${r.rejected} rejected and not imported.`);render()}
 else if(b=t.closest('#updSave')){try{const r=await api('PATCH','/students/'+b.dataset.id,{attendance:num('uA'),marks:num('uM'),assignments:num('uG')});PT='ov';toast('Saved. Score is now '+(r.student.risk.score??'-')+' ('+LB[r.student.risk.category]+').');render()}catch(x){fail('#uerr',x)}}
 else if(t.closest('#ivSave')){try{await api('POST','/interventions',{student_id:Number($('#vs').value)||null,category:$('#vc').value,priority:$('#vp').value,assignee_id:Number($('#vw').value),due_date:$('#vd').value,description:$('#vt').value.trim()});closeD();toast('Intervention created.');render()}catch(x){fail('#verr',x)}}
 else if(b=t.closest('[data-ivs]')){const [id,st]=b.dataset.ivs.split(':');await api('PATCH','/interventions/'+id,{status:st});toast('Updated.');render()}
 else if(b=t.closest('[data-done]'))drawer(`<h2 style="font-size:24px;margin:6px 0 4px">Complete intervention</h2><p class="nt">Completing records the outcome permanently.</p><label for="do">Outcome</label><select class="field" id="do"><option value="improved">Improved</option><option value="no_change">No change</option><option value="declined">Declined</option></select><label for="dn">Notes (optional)</label><textarea class="field" id="dn" rows="3"></textarea>${dmsg('derr')}<button class="btn" id="doneSave" data-id="${b.dataset.done}" style="margin-top:16px;width:100%">Record outcome</button>`);
 else if(b=t.closest('#doneSave')){try{const n=$('#dn').value.trim();await api('PATCH','/interventions/'+b.dataset.id,{status:'completed',outcome:$('#do').value,...(n?{notes:n}:{})});closeD();toast('Outcome recorded.');render()}catch(x){fail('#derr',x)}}
 else if(t.closest('[data-readall]')){await api('POST','/notifications/read-all');render()}
 else if(b=t.closest('[data-nid]')){await api('POST','/notifications/'+b.dataset.nid+'/read');if(b.dataset.sid)location.hash='#/students/'+b.dataset.sid;else render()}
 else if(t.closest('#cfSave')){const g=i=>Number($('#'+i).value),rules={medium:g('cf-med'),high:g('cf-high'),stale_days:g('cf-stale')};FACT.forEach(([f])=>rules[f]=[[g(`cf-${f}-0`),g(`cf-${f}-1`)],[g(`cf-${f}-2`),g(`cf-${f}-3`)]]);try{const r=await api('PUT','/rules',rules);toast(`Rules saved. ${r.recalculated} student${r.recalculated===1?'':'s'} recalculated.`);render()}catch(x){fail('#cferr',x)}}
 else if(t.closest('#pwSave')){try{await api('POST','/auth/password',{current:$('#pc').value,new:$('#pn').value});$('#pc').value=$('#pn').value='';$('#pe').classList.add('hide');toast('Password updated.')}catch(x){fail('#pe',x)}}
 else if(b=t.closest('[data-usr]')){const [id,a]=b.dataset.usr.split(':');await api('PATCH','/users/'+id,a==='courses'?{courses:$('#uc'+id).value.split(',').map(x=>x.trim()).filter(Boolean)}:{active:a==='on'});toast('Account updated.');render()}
}));
let IMP='';
document.addEventListener('change',e=>act(async()=>{const t=e.target;
 if(t.id==='fc'){SF.course=t.value;SF.page=1;render()}else if(t.id==='fr'){SF.category=t.value;SF.page=1;render()}
 else if(t.id==='fis'){IF.status=t.value;render()}else if(t.id==='fip'){IF.priority=t.value;render()}
 else if(t.id==='imf'){const f=t.files[0];if(!f)return;if(f.size>500000)return fail('#imerr',new Error('That file is larger than 500 KB.'));$('#imt').value=await f.text();$('#imPrev').click()}}));
let qt;$('#q').addEventListener('input',e=>{clearTimeout(qt);qt=setTimeout(()=>{SF.q=e.target.value.trim();SF.page=1;if(route().k==='students'&&!route().id)render();else location.hash='#/students'},250)});
document.addEventListener('keydown',e=>{if(e.key==='Escape')closeD();if(e.key==='Enter'&&e.target.matches('tr.rd'))location.hash=e.target.dataset.href});
// ---- Analytics, guide, product tour ----
ICON.analytics='<path d="M4 20V4M4 20h16M8 16v-5M13 16V8M18 16v-8"/>';
const CCOL={high:'#dc2626',medium:'#d97706',low:'#16a34a',incomplete:'#94a3b8'};
function scatter(L,R){const W=560,H=300,Lm=44,B=34,cl=(v,a,b)=>Math.max(a,Math.min(b,v)),x=v=>Lm+(cl(v,30,100)-30)/70*(W-Lm-14),y=v=>H-B-(cl(v,20,100)-20)/80*(H-B-14),P=L.filter(s=>s.attendance!=null&&s.marks!=null);
 return `<svg viewBox="0 0 ${W} ${H}" width="100%" role="img" aria-label="Each dot is a student plotted by attendance and marks">${[30,50,70,90].map(v=>`<line x1="${x(v)}" x2="${x(v)}" y1="14" y2="${H-B}" stroke="var(--ln)"/><text x="${x(v)}" y="${H-14}" text-anchor="middle" font-size="11" fill="var(--mut)">${v}%</text>`).join('')}${[20,40,60,80,100].map(v=>`<line x1="${Lm}" x2="${W-14}" y1="${y(v)}" y2="${y(v)}" stroke="var(--ln)"/><text x="${Lm-6}" y="${y(v)+4}" text-anchor="end" font-size="11" fill="var(--mut)">${v}</text>`).join('')}${R.attendance.map(([t])=>`<line x1="${x(t)}" x2="${x(t)}" y1="14" y2="${H-B}" stroke="var(--high)" stroke-dasharray="4 4" opacity=".7"/>`).join('')}${R.marks.map(([t])=>`<line x1="${Lm}" x2="${W-14}" y1="${y(t)}" y2="${y(t)}" stroke="var(--high)" stroke-dasharray="4 4" opacity=".7"/>`).join('')}<text x="${W/2}" y="${H-1}" text-anchor="middle" font-size="11" fill="var(--mut)">Attendance</text>${P.map(s=>`<a href="#/students/${s.id}"><circle cx="${x(s.attendance)}" cy="${y(s.marks)}" r="7" fill="${CCOL[s.risk.category]}" stroke="var(--card)" stroke-width="2"><title>${esc(s.name)}: attendance ${s.attendance}%, marks ${s.marks}%, ${LB[s.risk.category]}</title></circle></a>`).join('')}</svg>`}
V.analytics=async()=>{const [sm,st,ru,tr]=await Promise.all([api('GET','/reports/summary'),api('GET','/students?per_page=100'),api('GET','/rules'),api('GET','/reports/attendance-trend')]),R=ru.rules,c=k=>sm.by_category[k]||0,n=sm.students||1,S2=st.students,sc=S2.filter(s=>s.risk.score!=null),avg=sc.length?Math.round(sc.reduce((t,s)=>t+s.risk.score,0)/sc.length):0,stale=S2.filter(s=>s.outdated).length,ivs=sm.interventions_by_status,oc=sm.outcomes,done=Object.values(oc).reduce((a,b)=>a+b,0);
 return head('Analytics','Breakdowns from the records you are allowed to see.',pdfBtn.replace('btn','btn s'))+`<div class="grid">${kpi(1,sm.students,'Students in view','var(--p2)')}${kpi(2,avg,'Average risk score','var(--med)')}${kpi(3,c('high')+c('medium'),'Medium or high risk','var(--high)')}${kpi(4,stale+c('incomplete'),'Outdated or incomplete records','var(--mut)')}
 <div class="card c4"><h2>Risk distribution</h2><p class="nt">Select a row to open that group</p><div class="stk">${['high','medium','low','incomplete'].map(k=>`<i style="flex:${c(k)||.001};background:${CCOL[k]}"></i>`).join('')}</div>${['high','medium','low','incomplete'].map(k=>`<a class="lk" style="text-decoration:none" href="#/students" data-cat="${k}">${pill(k)}<span class="w"></span><b>${c(k)}</b></a>`).join('')}</div>
 <div class="card c8"><h2>Attendance and marks</h2><p class="nt">Dashed lines are the current thresholds. Select a dot to open the student. Students with missing figures are not plotted.</p>${scatter(S2,R)}${st.total>100?'<p class="nt">Showing the first 100 students.</p>':''}</div>
 ${trendCard(tr)}<div class="card c6"><h2>Average risk score by course</h2><p class="nt">Select a course to open its students</p>${sm.by_course.map(x=>`<a class="lk" style="text-decoration:none;display:block" href="#/students" data-course="${esc(x.course)}"><div style="display:flex;justify-content:space-between"><span>${esc(x.course)} <small style="color:var(--mut)">${x.students} students</small></span><b>${x.average_score}</b></div><div class="trk" style="margin-top:5px"><i style="width:${x.average_score}%"></i></div></a>`).join('')||'<p class="empty">No data.</p>'}</div>
 <div class="card c6"><h2>Main contributing factors</h2><p class="nt">Students with points from each factor</p>${Object.entries(sm.factors).map(([k,v])=>`<div class="fac"><div class="t"><span>${esc(k)}</span><b>${v} of ${n}</b></div><div class="trk"><i style="width:${v/n*100}%"></i></div></div>`).join('')||'<p class="empty">No factors yet.</p>'}
 <h2 style="margin-top:18px">Interventions</h2>${['planned','in_progress','completed','cancelled'].map(k=>`<div class="wl"><span class="w">${k.replace('_',' ')}</span><b>${ivs[k]||0}</b></div>`).join('')}${done?`<p class="nt" style="margin-top:8px">Outcomes of ${done} completed: ${Object.entries(oc).map(([k,v])=>v+' '+k.replace('_',' ')).join(', ')}. ${esc(sm.note)}</p>`:'<p class="nt" style="margin-top:8px">No completed interventions yet.</p>'}</div></div>`};
// guide
const ARL={admin:'Administrator',faculty:'Faculty',support:'Student support'};
const RG={admin:['Open the Dashboard to see how many students are at each risk level.','Approve new accounts and set faculty courses in Settings.','Open Students to search, filter and sort. Use Add student or Import CSV (with preview) to add records.','Open a student to see the score, the factors behind it and the full score history.','In Risk rules, change a threshold and save. Every student is recalculated and the change is audited.','In Analytics, select a risk level or a course to open that group.'],faculty:['Your dashboard lists only students in your assigned courses.','Open a student who needs attention and read why the score is what it is.','When marks or attendance change, use Update records. The score recalculates and the change is kept in the history.','Use New intervention to plan support, with an owner and a follow-up date.','Check My follow-ups so nothing is missed.'],support:['Your dashboard groups follow-ups into Overdue and This week.','Under New concerns, choose Start support for any high-risk student with no active help.','Create the intervention with an owner, a category, a date and a planned action.','Use Start when work begins, and Complete to record the outcome.','Watch Alerts for risk changes and overdue follow-ups.']};
const FQ=[['Does a high score mean a student will drop out?','No. The score is an illustrative indicator that suggests a student may benefit from a conversation. It is not a proven prediction, and it never triggers automatic action.'],['How is the score calculated?','It adds points for attendance, marks and assignment completion using bands set in Risk rules, capped at 100. Medium and High start at administrator-set values. Every score shows its factors so you can see exactly why.'],['Who can see which students?','Administrators and student-support staff see every student. Faculty see only students in their assigned courses. The server enforces this, not just the screen.'],['Where is my data stored?','In the server database. It stays after you sign out or reload.'],['How do alerts work?','An alert is created when something really changes: a student moves to a higher risk level, an intervention is assigned or completed, or a follow-up date passes. The same event never creates a second alert.'],['What happens when data is missing or outdated?','An empty figure is stored as missing and the student shows Data incomplete, never low risk. A record not updated for the number of days set in Risk rules is flagged Outdated, with a warning.'],['Can I import or export CSV files?','Administrators can import a CSV with a preview, validation and duplicate checks. Everyone can export the students they are allowed to see.']];
V.guide=async()=>{const rt=window.gtab||ME.role,fl=[['Student data','Attendance, marks and assignment completion'],['Risk assessment','Points are added and explained'],['Review and alerts','Staff are told what changed'],['Support intervention','A person plans help'],['Follow-up','Dates keep support on track'],['Progress monitoring','Outcomes and trends show what helps']];
 return `<div class="guide"><div class="card hero2"><h1>Project guide</h1><p>DropoutAlert helps colleges notice students who may need support earlier, understand why, and organise timely help. It is a support tool, not a system for labelling or punishing students.</p><button class="btn" data-tour>Start the product tour</button></div>
 <h2 class="gh">How it works</h2><div class="flow">${fl.map(([t,d],i)=>`<div class="fs rise" style="--i:${i}"><b class="n">${i+1}</b><b>${t}</b><small>${d}</small></div>`).join('')}</div>
 <div class="two" style="margin-top:22px"><div class="card"><h2>What it does</h2><ul class="gl"><li>Flags students who may need support, with the reasons shown.</li><li>Tracks interventions, follow-ups and outcomes.</li><li>Raises alerts from real changes in the records.</li><li>Lets administrators adjust the scoring rules openly.</li></ul></div><div class="card"><h2>What it does not claim</h2><ul class="gl"><li>It does not predict who will drop out.</li><li>It does not decide anything. A person reviews every case.</li><li>It does not use personal characteristics such as gender or religion.</li><li>Missing data is never read as good performance.</li></ul></div></div>
 <h2 class="gh">Guides by role</h2><div class="tabs" role="group" aria-label="Role guides">${Object.keys(ARL).map(r=>`<button data-gtab="${r}" aria-pressed="${rt===r}">${ARL[r]}</button>`).join('')}</div><div class="card"><ol class="gl">${RG[rt].map(x=>`<li>${x}</li>`).join('')}</ol></div>
 <h2 class="gh">Frequently asked questions</h2><div class="card faq"><input class="field faqq" placeholder="Search the FAQ" aria-label="Search the FAQ" style="margin-bottom:8px">${FQ.map(([q,a])=>`<details data-q="${(q+' '+a).toLowerCase()}"><summary>${q}</summary><p>${a}</p></details>`).join('')}<p class="faqn" hidden>No answers match. Try a different word.</p></div>
 <h2 class="gh">Troubleshooting</h2><div class="card"><ul class="gl"><li><b>I cannot sign in.</b> New accounts must be approved by an administrator first. Too many wrong attempts pauses sign-in for a few minutes.</li><li><b>I cannot see a student.</b> Faculty see only their assigned courses. Ask an administrator to update them.</li><li><b>I did not get a reset email.</b> The server must have email configured, and the message says the same thing whether or not the address exists.</li><li><b>Fonts look different.</b> Fonts load from the internet. Offline, a standard font is used.</li></ul></div></div>`};
// tour
let tourI=0,tourS=[];
const TOUR=[{t:'Welcome to DropoutAlert',d:'A short tour of where things are. You can skip it now and reopen it with the ? button at any time.'},{k:'mine',t:'My progress',d:'Your own attendance, marks and assignments, and the support available to you.'},{k:'dash',t:'Dashboard',d:'Your starting point. It shows who may need support and what is driving the scores.'},{k:'students',t:'Students',d:'Search, filter and sort every student, then open a profile to see exactly why a score is what it is.'},{k:'interventions',t:'Interventions',d:'Plan support with an owner and a date, then record the outcome.'},{k:'analytics',t:'Analytics',d:'Breakdowns and a chart of every student. Select a chart item to open that group.'},{k:'alerts',t:'Alerts',d:'Notifications created by real changes, such as a student moving to a higher risk level.'},{k:'rules',t:'Risk rules',d:'Administrators adjust the scoring rules here. Saving recalculates every student.'},{k:'settings',t:'Settings',d:'Your password and, for administrators, account approval and the audit trail.'},{k:'guide',t:'Guide',d:'Role guides, the FAQ and troubleshooting live here.'},{t:'You are ready',d:'Remember: scores are indicators for human review, never automatic decisions.'}];
function showTour(){let o=$('#tour');if(!o){o=document.createElement('div');o.id='tour';document.body.appendChild(o)}
 const st=tourS[tourI],el=st.k?document.querySelector(`#side [data-href="#/${st.k}"]`):null,r=el&&el.offsetParent?el.getBoundingClientRect():null,last=tourI===tourS.length-1;
 o.innerHTML=(r?`<div class="spot" style="left:${r.left-4}px;top:${r.top-4}px;width:${r.width+8}px;height:${r.height+8}px"></div>`:'<div class="spot0"></div>')+`<div class="pop" role="dialog" aria-label="Product tour" style="${r?`left:${Math.min(r.right+16,innerWidth-340)}px;top:${Math.max(12,Math.min(r.top,innerHeight-240))}px`:'inset:0;margin:auto;height:fit-content'}"><small>Step ${tourI+1} of ${tourS.length}</small><h3>${st.t}</h3><p>${st.d}</p><div class="tr"><button class="link" data-tskip>${last?'Close':'Skip tour'}</button><span>${tourI?'<button class="btn s" data-tprev>Back</button> ':''}<button class="btn" data-tnext>${last?'Finish':'Next'}</button></span></div></div>`;const nb=o.querySelector('[data-tnext]');if(nb)nb.focus()}
const startTour=()=>{tourS=TOUR.filter(x=>!x.k||NAVS().some(n=>n[0]===x.k));tourI=0;showTour()};
function endTour(done){const o=$('#tour');if(o)o.remove();if(done){try{localStorage.setItem('da-tour','1')}catch(e){}toast('Tour finished. Reopen it any time with the ? button.')}}
function tourHint(){try{if(!localStorage.getItem('da-tour'))setTimeout(()=>toast('New here? Press the ? button in the top bar for a short tour.'),900)}catch(e){}}
$('#theme').insertAdjacentHTML('beforebegin','<button class="ib" id="tourBtn" aria-label="Start product tour" title="Product tour">?</button>');
document.addEventListener('click',e=>{const t=e.target;let b;
 if(b=t.closest('[data-cat]')){SF.category=b.dataset.cat;SF.course='';SF.page=1}
 else if(b=t.closest('[data-gtab]')){window.gtab=b.dataset.gtab;render()}
 else if(t.closest('[data-tour]')||t.closest('#tourBtn'))startTour();
 else if(t.closest('[data-tnext]')){tourI++;tourI>=tourS.length?endTour(true):showTour()}
 else if(t.closest('[data-tprev]')){tourI--;showTour()}
 else if(t.closest('[data-tskip]'))endTour(false)});
document.addEventListener('input',e=>{if(e.target.matches('.faqq')){const q=e.target.value.toLowerCase(),g=e.target.closest('.guide');let n=0;g.querySelectorAll('.faq details').forEach(d=>{const m=d.dataset.q.includes(q);d.hidden=!m;if(m)n++});g.querySelector('.faqn').hidden=n>0}});
document.addEventListener('keydown',e=>{if(e.key==='Escape'&&$('#tour'))endTour(false)});
addEventListener('resize',()=>{if($('#tour'))showTour()});

// ---- Attendance history, trend chart, follow-up calendar ----
const dshort=d=>new Date(d+'T00:00:00').toLocaleDateString('en-IN',{day:'numeric',month:'short'});
function tline(pts,w=640,h=170){if(pts.length<2)return '<p class="nt">At least two weekly readings are needed to show a trend.</p>';
 const x=i=>34+i*(w-54)/(pts.length-1),y=v=>h-26-v/100*(h-46),d=pts.map((p,i)=>`${i?'L':'M'}${x(i)} ${y(p.v)}`).join(' '),step=Math.ceil(pts.length/6);
 return `<svg viewBox="0 0 ${w} ${h}" width="100%" role="img" aria-label="Attendance by week, from ${pts[0].v.toFixed(0)} to ${pts[pts.length-1].v.toFixed(0)} percent">${[0,50,100].map(t=>`<line x1="34" x2="${w-20}" y1="${y(t)}" y2="${y(t)}" stroke="var(--ln)"/><text x="28" y="${y(t)+4}" text-anchor="end" font-size="11" fill="var(--mut)">${t}%</text>`).join('')}<path d="${d}L${x(pts.length-1)} ${h-26}L${x(0)} ${h-26}Z" fill="var(--bar)" opacity=".1"/><path class="dl" pathLength="1" d="${d}" fill="none" stroke="var(--bar)" stroke-width="3" stroke-linejoin="round"/>${pts.map((p,i)=>`<circle cx="${x(i)}" cy="${y(p.v)}" r="4.5" fill="var(--card)" stroke="var(--bar)" stroke-width="2.5"><title>Week of ${dshort(p.l)}: ${p.v.toFixed(1)}%</title></circle>${i%step===0?`<text x="${x(i)}" y="${h-6}" text-anchor="middle" font-size="10.5" fill="var(--mut)">${dshort(p.l)}</text>`:''}`).join('')}</svg>`}
const trendCard=tr=>`<div class="card c12"><h2>Average attendance by week</h2><p class="nt">${esc(tr.note)}</p>${tline(tr.weeks.map(w=>({v:w.average,l:w.week_start})))}</div>`;
const attTab=(s,L,can)=>`<div class="grid"><div class="card c8"><h2>Attendance by week</h2><p class="nt">Latest reading: ${pc(s.attendance)}. Each point is a reading that was recorded for this student.</p>${tline(L.map(r=>({v:r.percent,l:r.week_start})))}${L.length?`<div class="tw"><table style="margin-top:10px"><tr><th>Week starting</th><th>Attendance</th></tr>${[...L].reverse().slice(0,8).map(r=>`<tr><td>${dshort(r.week_start)}</td><td>${r.percent}%</td></tr>`).join('')}</table></div>`:''}</div>${can?`<div class="card c4"><h2>Record a weekly reading</h2><p class="nt">Recording the newest week updates the current figure and the score. An older week only fills in the history.</p><label for="aw">Week</label><input class="field" id="aw" type="date" value="${new Date().toISOString().slice(0,10)}" max="${new Date().toISOString().slice(0,10)}"><label for="ap">Attendance %</label><input class="field" id="ap" type="number" min="0" max="100"><div class="msg err hide" id="aterr" role="alert"></div><button class="btn" id="attSave" data-id="${s.id}" style="margin-top:14px">Save reading</button></div>`:''}</div>`;
// calendar
let IVW='list',CM=new Date();CM.setDate(1);
const fdate=(y,m,d)=>`${y}-${String(m+1).padStart(2,'0')}-${String(d).padStart(2,'0')}`;
async function calView(){const d=await api('GET','/interventions'),y=CM.getFullYear(),m=CM.getMonth(),lead=(new Date(y,m,1).getDay()+6)%7,days=new Date(y,m+1,0).getDate(),today=fdate(...(()=>{const t=new Date();return[t.getFullYear(),t.getMonth(),t.getDate()]})()),by={};
 d.interventions.forEach(i=>(by[i.due_date]=by[i.due_date]||[]).push(i));
 const cls=i=>['completed','cancelled'].includes(i.status)?'dn':i.overdue?'od':i.status==='planned'?'pl':'ip';
 let cells=['Mon','Tue','Wed','Thu','Fri','Sat','Sun'].map(x=>`<div class="h">${x}</div>`).join('')+'<div></div>'.repeat(lead);
 for(let k=1;k<=days;k++){const key=fdate(y,m,k),L=by[key]||[];cells+=`<div class="d ${key===today?'t':''}"><b>${k}</b>${L.slice(0,3).map(i=>`<a class="${cls(i)}" href="#/students/${i.student_id}" title="${esc(i.student_name)}: ${esc(i.category)} (${i.status.replace('_',' ')})">${esc(i.student_name.split(' ')[0])}, ${esc(i.category)}</a>`).join('')}${L.length>3?`<small style="color:var(--mut)">+${L.length-3} more</small>`:''}</div>`}
 return `<div style="display:flex;align-items:center;justify-content:space-between;margin-bottom:12px;flex-wrap:wrap;gap:8px"><h2 style="font:600 18px Inter,sans-serif">${CM.toLocaleDateString('en-IN',{month:'long',year:'numeric'})}</h2><span><button class="btn s" data-cm="-1" style="padding:5px 12px">Previous</button> <button class="btn s" data-cm="0" style="padding:5px 12px">Today</button> <button class="btn s" data-cm="1" style="padding:5px 12px">Next</button></span></div><div class="cal">${cells}</div><p class="nt" style="margin-top:12px"><span class="p high">Overdue</span> <span class="p medium">Planned</span> <span class="p t">In progress</span> <span class="p low">Done</span> Select an item to open the student.</p>`}
const ivToggle=()=>`<div class="chips" style="margin-bottom:14px" role="group" aria-label="View">${[['list','List'],['cal','Calendar']].map(([k,l])=>`<button class="chip" data-ivview="${k}" aria-pressed="${IVW===k}">${l}</button>`).join('')}</div>`;
V.interventions=async()=>{if(IVW==='cal')return head('Interventions','Follow-up dates at a glance.','<button class="btn" data-newiv="">New intervention</button>')+ivToggle()+await calView();
 return (await V.interventionsList()).replace('<div class="fl">',ivToggle()+'<div class="fl">')};
document.addEventListener('click',async e=>{const t=e.target;let b;
 if(b=t.closest('[data-ivview]')){IVW=b.dataset.ivview;render()}
 else if(b=t.closest('[data-cm]')){const v=+b.dataset.cm;if(v===0){CM=new Date();CM.setDate(1)}else CM=new Date(CM.getFullYear(),CM.getMonth()+v,1);render()}
 else if(b=t.closest('#attSave')){try{const p=$('#ap').value.trim();await api('POST','/students/'+b.dataset.id+'/attendance',{week_start:$('#aw').value,percent:p===''?null:Number(p)});toast('Reading saved.');render()}catch(x){const m=$('#aterr');if(m){m.textContent=emsg(x);m.classList.remove('hide')}}}});

// ---- polish: skeleton, count-up, banner, bulk actions, preferences, profile name ----
let SEL=new Set();
const ROLEN={admin:'Administrator',faculty:'Faculty',support:'Student support',student:'Student'};
const skel=()=>`<div role="status" aria-label="Loading"><div class="sk sk-h"></div><div class="sk-r"><i class="sk"></i><i class="sk"></i><i class="sk"></i><i class="sk"></i></div><div class="sk sk-b"></div></div>`;
const reduced=()=>window.matchMedia&&matchMedia('(prefers-reduced-motion:reduce)').matches;
function countUp(){if(reduced())return;$$('.kpi .k').forEach(el=>{const n=parseInt(el.textContent,10);if(isNaN(n)||String(n)!==el.textContent.trim())return;let t0;const st=ts=>{t0=t0||ts;const p=Math.min(1,(ts-t0)/800);el.textContent=Math.round(n*(1-Math.pow(1-p,3)));if(p<1)requestAnimationFrame(st)};el.textContent='0';requestAnimationFrame(st)})}
const banner=(gr,act)=>`<div class="ban"><div><small>${new Date().toLocaleDateString('en-IN',{weekday:'long',day:'numeric',month:'long'})}, ${ROLEN[ME.role]}</small><h1>${gr}, ${esc(ME.name)}</h1><p>Who may need support, and what is driving it.</p></div><div>${act}</div></div>`;
const bulkInner=()=>`<b>${SEL.size} selected</b><button class="btn" data-bulkiv>Create intervention for selected</button><button class="btn s" data-bulkclear>Clear selection</button>`;
const bulkBar=()=>`<div class="bulk" id="bulk" ${SEL.size?'':'hidden'}>${bulkInner()}</div>`;
function syncBulk(){const b=$('#bulk');if(!b)return;b.hidden=!SEL.size;b.innerHTML=bulkInner()}
const prefsCard=pr=>`<div class="card c6"><h2>Alert preferences</h2><p class="nt">Turned-off alert types are no longer created for you.</p>${[['risk','Risk category changes','A student moves to a higher risk level'],['overdue','Overdue follow-ups','A follow-up date has passed'],['assign','Assignments and outcomes','New or completed interventions']].map(([k,l,d])=>`<div class="wl"><span class="w">${l}<small>${d}</small></span><button class="sw" role="switch" aria-checked="${!!pr[k]}" aria-label="${l}" data-pref="${k}"></button></div>`).join('')}</div>`;
async function openBulk(){const us=ME.role==='admin'?await api('GET','/users'):null,staff=us?us.users.filter(u=>u.active):[ME],d=new Date();d.setDate(d.getDate()+7);
 drawer(`<h2 style="font-size:24px;margin:6px 0 4px">Intervention for ${SEL.size} student${SEL.size===1?'':'s'}</h2><p class="nt">One intervention is created for each selected student. Review each student’s context first.</p><label for="bc">Category</label><select class="field" id="bc">${['Attendance','Academic','Assignments','Mentoring','Wellbeing'].map(x=>`<option>${x}</option>`).join('')}</select><label for="bp">Priority</label><select class="field" id="bp"><option>high</option><option selected>medium</option><option>low</option></select><label for="bw">Assigned to</label><select class="field" id="bw">${staff.map(u=>`<option value="${u.id}" ${u.id===ME.id?'selected':''}>${esc(u.name)}</option>`).join('')}</select><label for="bd">Follow-up date</label><input class="field" id="bd" type="date" value="${d.toISOString().slice(0,10)}"><label for="bt">Planned action</label><textarea class="field" id="bt" rows="3"></textarea>${dmsg('berr')}<button class="btn" id="bulkSave" style="margin-top:16px;width:100%">Create ${SEL.size} intervention${SEL.size===1?'':'s'}</button>`)}
document.addEventListener('change',e=>{const t=e.target;
 if(t.matches('.rowck')){const id=+t.dataset.id;t.checked?SEL.add(id):SEL.delete(id);syncBulk()}
 else if(t.id==='allck'){$$('.rowck').forEach(c=>{c.checked=t.checked;const id=+c.dataset.id;t.checked?SEL.add(id):SEL.delete(id)});syncBulk()}});
document.addEventListener('click',async e=>{const t=e.target;let b;
 try{if(t.closest('[data-bulkclear]')){SEL.clear();$$('.rowck,#allck').forEach(c=>c.checked=false);syncBulk()}
 else if(t.closest('[data-bulkiv]'))await openBulk();
 else if(t.closest('#bulkSave')){try{const r=await api('POST','/interventions/bulk',{student_ids:[...SEL],category:$('#bc').value,priority:$('#bp').value,assignee_id:Number($('#bw').value),due_date:$('#bd').value,description:$('#bt').value.trim()});SEL.clear();closeD();toast(`${r.created} intervention${r.created===1?'':'s'} created.`);render()}catch(x){fail('#berr',x)}}
 else if(b=t.closest('[data-pref]')){const k=b.dataset.pref,on=b.getAttribute('aria-checked')==='true';await api('PUT','/auth/prefs',{[k]:!on});b.setAttribute('aria-checked',String(!on))}
 else if(t.closest('#nmSave')){const r=await api('PATCH','/auth/profile',{name:$('#pnm').value.trim()});ME=r.user;$('.me .av').textContent=ini(ME.name);$('.me span').textContent=ME.name;toast('Name updated.')}}
 catch(x){toast(emsg(x))}});

// ---- student view, saved filters, PDF links, account creation, help text ----
ICON.mine='<path d="M3 12 12 4l9 8M5 10v10h14V10"/>';
const pdfBtn='<a class="btn" href="/api/reports/summary.pdf" style="text-decoration:none">Download PDF report</a>';
// student's own page
V.mine=async()=>{const d=await api('GET','/me/student'),s=d.student,first=esc((s.name||'').split(' ')[0]),st={planned:'Planned',in_progress:'In progress',completed:'Completed'};
 const meter=(l,v)=>`<div class="fac"><div class="t"><span>${l}</span><b>${v==null?'Not recorded yet':v+'%'}</b></div><div class="trk"><i style="width:${v||0}%"></i></div></div>`;
 return `<div class="ban"><div><small>${new Date().toLocaleDateString('en-IN',{weekday:'long',day:'numeric',month:'long'})}, Student</small><h1>Hello, ${first}</h1><p>${esc(s.course)}. Here is how things look right now.</p></div><div><a class="btn" href="/api/me/report.pdf" style="text-decoration:none">Download my progress report</a></div></div>
 <div class="grid"><div class="card c4"><h2>My progress</h2><p class="nt">From your college records, updated ${s.updated?s.updated.slice(0,10):'recently'}.</p>${meter('Attendance',s.attendance)}${meter('Marks',s.marks)}${meter('Assignment completion',s.assignments)}</div>
 <div class="card c8"><h2>My attendance by week</h2><p class="nt">Each point is a reading from your college.</p>${tline(d.attendance.map(r=>({v:r.percent,l:r.week_start})))}</div>
 <div class="card c6"><h2>My support plan</h2><p class="nt">Help that has been arranged for you.</p>${d.support.length?d.support.map(i=>`<div class="wl"><span class="w"><b>${esc(i.category)} support</b><small>Follow-up date: ${i.due_date}</small></span><span class="p ${i.status==='completed'?'low':i.status==='in_progress'?'t':'medium'}">${st[i.status]||esc(i.status)}</span></div>`).join(''):'<p class="empty">There is no support plan at the moment. That is fine.</p>'}</div>
 <div class="card c6"><h2>Where to get help</h2><p class="nt">You can ask at any time.</p><ul class="gl">${d.resources.split('\n').filter(x=>x.trim()).map(x=>`<li>${esc(x)}</li>`).join('')}</ul></div></div>
 <p class="note">If something here looks wrong, please tell your faculty mentor so it can be corrected.</p>`};
// saved filters
let VIEWS=[],CURV='';
const viewsCtl=v=>{VIEWS=v;if(CURV&&!v.some(x=>String(x.id)===String(CURV)))CURV='';return `<select class="field sel" id="fsv" aria-label="Saved views"><option value="">Saved views</option>${v.map(x=>`<option value="${x.id}" ${String(x.id)===String(CURV)?'selected':''}>${esc(x.name)}</option>`).join('')}</select><button class="btn s" data-saveview>Save this view</button><button class="btn s" data-delview ${CURV?'':'disabled'}>Delete view</button>`};
document.addEventListener('change',e=>{if(e.target.id==='fsv'){CURV=e.target.value;const v=VIEWS.find(x=>String(x.id)===String(CURV));if(v){const p=v.params;SF.q=p.q||'';SF.course=p.course||'';SF.category=p.category||'';SF.sort=p.sort||'name';SF.order=p.order||'asc';SF.page=1;$('#q').value=SF.q}render()}});
document.addEventListener('click',async e=>{const t=e.target;
 try{if(t.closest('[data-saveview]'))drawer(`<h2 style="font-size:24px;margin:6px 0 4px">Save this view</h2><p class="nt">Saves the current search, filters and sorting. Only you can see it.</p><label for="svn">Name</label><input class="field" id="svn" maxlength="60" placeholder="For example: High risk in BBA">${dmsg('sverr')}<button class="btn" id="svSave" style="margin-top:16px;width:100%">Save view</button>`);
 else if(t.closest('#svSave')){try{const r=await api('POST','/views',{name:$('#svn').value.trim(),params:{q:SF.q,course:SF.course,category:SF.category,sort:SF.sort,order:SF.order}});CURV=r.view.id;closeD();toast('View saved.');render()}catch(x){fail('#sverr',x)}}
 else if(t.closest('[data-delview]')){const v=VIEWS.find(x=>String(x.id)===String(CURV));if(v)drawer(`<h2 style="font-size:24px;margin:6px 0 4px">Delete saved view?</h2><p class="nt">“${esc(v.name)}” will be removed. Your students and filters are not affected.</p><button class="btn" id="svDel" style="width:100%">Delete view</button>`)}
 else if(t.closest('#svDel')){await api('DELETE','/views/'+CURV);CURV='';closeD();toast('View deleted.');render()}
 // admin: create accounts and edit student help text
 else if(t.closest('#acctSave')){try{const role=$('#nr').value,x=$('#nx').value.trim(),b={name:$('#na').value.trim(),email:$('#ne').value.trim(),password:$('#np').value,role};if(role==='student')b.student_code=x;if(role==='faculty')b.courses=x.split(',').map(c=>c.trim()).filter(Boolean);await api('POST','/users',b);toast('Account created.');render()}catch(x){fail('#nerr',x)}}
 else if(t.closest('#resSave')){await api('PUT','/resources',{text:$('#rt').value});toast('Help text saved. Students see it now.')}}
 catch(x){toast(emsg(x))}});
const createAcctCard=()=>`<div class="card c12"><h2>Create an account</h2><p class="nt">Accounts you create are active at once. A student account is linked to one student by code, for example S1001.</p><div class="grid" style="gap:12px"><div class="c3"><label for="na">Name</label><input class="field" id="na"></div><div class="c3"><label for="ne">Email</label><input class="field" id="ne" type="email"></div><div class="c3"><label for="nr">Role</label><select class="field" id="nr"><option value="student">Student</option><option value="faculty">Faculty</option><option value="support">Student support</option><option value="admin">Administrator</option></select></div><div class="c3"><label for="np">Temporary password</label><input class="field" id="np" type="password" autocomplete="new-password"></div><div class="c6"><label for="nx">Student code (for students) or course names separated by commas (for faculty)</label><input class="field" id="nx"></div></div><div class="msg err hide" id="nerr" role="alert"></div><button class="btn" id="acctSave" style="margin-top:12px">Create account</button></div>`;
const resCard=t=>`<div class="card c12"><h2>Help text for students</h2><p class="nt">Shown on every student’s page and in their PDF. One point per line. Use your college’s real contacts.</p><textarea class="field" id="rt" rows="4">${esc(t)}</textarea><button class="btn" id="resSave" style="margin-top:12px">Save help text</button></div>`;

boot();
'''


app = create_app() if os.environ.get("DROPOUTALERT_NO_AUTOAPP") != "1" else None

if __name__ == "__main__":
    app.run(host=os.environ.get("HOST", "127.0.0.1"), port=int(os.environ.get("PORT", "5000")))
