# DropoutAlert – Student Dropout Early Warning System

A support tool that helps colleges notice students who may need help earlier, see **why**, and organise
timely, human-led support.

> Scores are **illustrative indicators for human review**. They are not validated predictions of dropout,
> and nothing in this system acts on a student automatically.

The whole application is **one Python file**, `dropoutalert.py`: database models, API, risk engine, login
and permissions, PDF reports and the complete web interface. Everything else in this folder is optional
(deployment files, tests, a standalone demo).

## What is in this folder

| File | Purpose |
|---|---|
| `dropoutalert.py` | **The application.** This is the only file the server needs. |
| `requirements.txt` | Libraries to install on the server. |
| `Procfile` | Start command for hosts that read one (Railway, Heroku-style). |
| `Dockerfile` | Optional container build (not tested here, no Docker was available). |
| `.env.example` | Every setting, with comments. |
| `tests/`, `pytest.ini`, `requirements-dev.txt` | 114 automated tests. |
| `extras/prototype-demo.html` | A separate browser-only demo with fake data. Not connected to the server. |

## Who can do what

| Role | Access |
|---|---|
| Administrator | Everything: accounts, scoring rules, student help text, audit trail, CSV import |
| Faculty | Only students in their assigned courses: records, attendance, interventions |
| Student support | All students' progress and interventions; cannot edit marks or attendance |
| Student | Only their **own** attendance, marks, assignments, support plan and help text. No risk score and no staff notes. |

Features: dashboards per role, student directory (search, filters, sorting, saved views, bulk actions),
student profile with score explanation and history, weekly attendance history, interventions (list and
calendar), alerts with preferences, analytics, risk-rule editor, CSV import (with preview) and export,
PDF reports, audit trail, project guide and product tour, dark mode.

## 1. Try it on your own computer first

Needs Python 3.10 or newer.

```bash
pip install -r requirements.txt
```

Set these (Mac/Linux use `export NAME=value`; Windows PowerShell uses `$env:NAME="value"`):

```
SECRET_KEY      any long random text
ADMIN_EMAIL     you@college.edu
ADMIN_PASSWORD  Choose-a-Strong-1      (8+ characters, with a letter and a number)
SEED_DEMO       1                      (optional: fictional demo users and students)
```

Then:

```bash
python dropoutalert.py
```

Open http://127.0.0.1:5000. With `SEED_DEMO=1` you can sign in as `admin@dropoutalert.demo`,
`faculty@dropoutalert.demo` or `support@dropoutalert.demo` (password `demo1234`). The data is fictional.

## 2. Deploy

Any host that runs Python works. These are the settings it needs:

- **Install:** `pip install -r requirements.txt`
- **Start:** `gunicorn -w 2 -b 0.0.0.0:$PORT dropoutalert:app`
- **Health check path:** `/healthz`

### Environment variables

| Name | Value |
|---|---|
| `APP_ENV` | `production` (requires `SECRET_KEY` and `PUBLIC_URL`, makes cookies Secure) |
| `SECRET_KEY` | long random text, secret, the same on every worker |
| `PUBLIC_URL` | your site address, for example `https://alerts.yourcollege.edu` |
| `DATABASE_URL` | PostgreSQL address. `postgres://` is accepted and converted. |
| `TRUST_PROXY` | `1` when the host puts HTTPS in front of the app (most do) |
| `ADMIN_EMAIL`, `ADMIN_NAME`, `ADMIN_PASSWORD` | creates the first administrator once, if none exists |

Optional: `LOGIN_IMAGE_URL`, `SMTP_*` (see `.env.example`).

### Example: Render (manual setup)

1. Put `dropoutalert.py` and `requirements.txt` in a GitHub repository.
2. In Render create a **PostgreSQL** database and copy its internal connection URL.
3. Create a **Web Service** from the repository. Use the install and start commands above.
4. Add the environment variables from the table. Set `PUBLIC_URL` to the address Render gives you
   (change it and redeploy if the address differs from what you guessed).
5. Open `https://your-address/healthz`. You should see `{"status":"ok"}`.

Check Render's current pricing and free-tier terms before you rely on them. When this was written, free web
services went to sleep after about 15 minutes without traffic (the next visit waits 30 to 60 seconds), and the
free PostgreSQL database expired after about 30 days. **Do not keep real student data on a database that
can expire.** Use a paid database, or a server your college controls.

## 3. After the first deploy

1. Sign in with the administrator you created, then **remove `ADMIN_PASSWORD`** from the environment.
2. **Never set `SEED_DEMO` on a public site.** It would create accounts with a known password.
3. Import students: Students, then Import CSV. Columns: `name, course, attendance, marks, assignments`.
   An empty number is stored as *missing* and shown as "Data incomplete", never as low risk.
4. Settings, then **Create an account** for faculty, support staff and students.
   A student account links to one student by code (for example `S1001`).
5. Settings, then **Help text for students**: put your college's real contacts there.
6. Review and adjust the scoring rules in **Risk rules** with your counsellors.
7. Optional: a licensed campus photo URL in `LOGIN_IMAGE_URL`; SMTP settings for real reset emails.
8. **Back up the database on a schedule** (`pg_dump` for PostgreSQL) and practise restoring it once.

## Security notes

- Passwords are hashed. Sessions use HttpOnly, SameSite and (in production) Secure cookies, and end after
  8 hours. Changing a password, deactivating a user or changing a role ends their other sessions.
- Wrong-password attempts are limited (5 per 5 minutes per email), stored in the database so the limit holds
  across workers.
- Every role is enforced on the server, not just hidden in the interface. Faculty cannot read other courses.
  Students cannot reach any staff endpoint.
- Password-reset links are single use, expire after 30 minutes, and only a hash is stored. Without
  `SMTP_HOST` they are only written to the server log, and the app never claims an email was sent.
- Audit events are recorded for sign-ins, record changes, rule changes, exports and reports. Passwords are never logged.
- Reports and exports contain personal student data. Share them only with authorised staff.

## Running the tests

```bash
pip install -r requirements-dev.txt
python -m pytest -q
```

## Honest limitations

- **Not checked by eye in many real browsers.** Layout, animation and mobile behaviour were verified with
  scripted tests against a running server, and the PDFs were rendered and inspected. Please look at it yourself.
- Verified on SQLite. **PostgreSQL, real email delivery and your HTTPS host were not tested here.**
- PDF reports use standard fonts, so characters outside Western European alphabets (for example Tamil) print as `?`.
- Tables are created automatically at start-up. For later schema changes use a migration tool such as Alembic.
- There is no real-time push. Alerts appear when someone loads the page. For overdue-follow-up alerts without
  anyone opening the app, run `flask --app dropoutalert run-rules` from a scheduler.
- No real campus photography is included; the sign-in page uses an illustration unless you set `LOGIN_IMAGE_URL`.
- Scoring rules are illustrative defaults. Agree them with your institution before relying on them.
