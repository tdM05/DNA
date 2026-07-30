# Lean Faithfulness Survey Hosting Repo

This repository is a deployable copy of the faithfulness survey website and the two Lean formalization projects it compares.

Layout:

```text
LeanEuclidF/        # Formalization B and the survey web server
LeanEuclid/            # Formalization A
deploy/               # systemd and Caddy templates
```

The survey server lives at:

```text
LeanEuclidF/eval/survey/server.py
```

Run it from `LeanEuclidF/` with:

```bash
eval/survey/launch_survey.sh
```

The launch script loads:

```text
LeanEuclidF/eval/survey/survey.env
```

That file is intentionally not committed because it contains deployment secrets.

## Important Runtime Assumptions

- `LeanEuclidF/` and `LeanEuclid/` must stay as sibling directories.
- `LeanEuclidF/eval/survey/data/survey_data.json` uses relative roots:
  - Formalization A: `../LeanEuclid`
  - Formalization B: `.`
- The Python server should bind to `127.0.0.1:8765`.
- Put Caddy or Nginx in front for public HTTP/HTTPS.
- Do not expose port `8765` directly to the internet.
- Do not commit `survey.env`, reviewer files, response SQLite DBs, admin password hashes, logs, or PID files. Configure the admin password through `survey.env` or service environment variables on the VM.

## VM Setup Steps

These instructions are written for an Ubuntu VM such as AWS Lightsail.

### 1. Install System Packages

```bash
sudo apt update
sudo apt install -y git curl build-essential python3 python3-venv python3-pip sqlite3 tmux caddy
```

Install `elan`:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
source ~/.bashrc
```

### 2. Clone The Repo

Use the path expected by the service template, or adjust the template later:

```bash
sudo mkdir -p /opt
sudo chown "$USER:$USER" /opt
cd /opt
git clone REPLACE_WITH_GITHUB_URL lean-faithfulness-survey-hosting
cd lean-faithfulness-survey-hosting
```

### 3. Install Solver Binaries

Both Lean projects call external SMT tools through `smt-portfolio`, `z3`, and `cvc5`.

Known issue: method A and method B do not reliably tolerate exactly the same solver stack. Keep the solver paths method-specific.

Method B known-working stack:

```text
Lean toolchain: leanprover/lean4:v4.8.0-rc2
mathlib rev: 7906a8a3488af5112e84d792d0d394b6c49026f0
smt rev: 49f428c5e0feebae8afcf47b037a4f5a0e4bcc62
smt-portfolio: 1.0.0
z3 binary: 4.15.4
z3-solver pip package: 4.15.4.0
cvc5 binary/pip package: 1.3.4
```

Method A known-working stack:

```text
Lean toolchain: leanprover/lean4:v4.19.0
mathlib rev: c44e0c8ee63ca166450922a373c7409c5d26b00b
smt rev: 072014eeeef08c6731a8a5a12761bfdaea8ce987
smt-portfolio: 1.0.0
z3 binary: 4.14.2
cvc5 binary: 1.2.2-dev.159.82ff0f2f3
cvc5 git: 82ff0f2f3
```

Important Method A caveat: the source environment used to validate Method A reported local modifications inside `.lake/packages/smt` at the `smt` revision above. Those exact modifications are included in this repo as:

```text
deploy/patches/method-a-lean-smt-local.patch
```

After Lake has downloaded Method A dependencies, apply the patch before building Method A:

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclid
lake update
git -C .lake/packages/smt apply /opt/lean-faithfulness-survey-hosting/deploy/patches/method-a-lean-smt-local.patch
git -C .lake/packages/smt status --short
```

The status output should show modifications to `Smt/*.lean` and `Smt/Tactic/*.lean`. Then run `lake build Book`. If Method A fails on the VM even with the solver binaries above, inspect `.lake/packages/smt` first rather than changing survey code.

On the VM, create separate solver environments/paths. Method B can be installed with pip:

```bash
python3 -m venv /opt/method-b-solver
/opt/method-b-solver/bin/pip install --upgrade pip
/opt/method-b-solver/bin/pip install smt-portfolio==1.0.0 z3-solver==4.15.4.0 cvc5==1.3.4
```

Verify Method B:

```bash
/opt/method-b-solver/bin/smt-portfolio --help >/dev/null
/opt/method-b-solver/bin/z3 --version
/opt/method-b-solver/bin/cvc5 --version
```

Method A should use a separate directory containing `smt-portfolio`, `z3`, and `cvc5` matching the Method A versions above. The known-working Method A `cvc5` is a development binary, not a normal pip pin. If an exact binary is unavailable, use the closest available Method A solver stack, then verify with `lake build Book`; do not assume the Method B solver stack is acceptable for Method A.

Verify Method A:

```bash
/opt/method-a-solver/bin/smt-portfolio --help >/dev/null
/opt/method-a-solver/bin/z3 --version
/opt/method-a-solver/bin/cvc5 --version
```

Expected version output should include:

```text
Z3 version 4.14.2 - 64 bit
This is cvc5 version 1.2.2-dev.159.82ff0f2f3
```

### 4. Fetch Lean Dependencies And Build

Build method B:

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclidF
PATH="/opt/method-b-solver/bin:$HOME/.elan/bin:$PATH" lake build Book1
```

Build method A:

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclid
PATH="/opt/method-a-solver/bin:$HOME/.elan/bin:$PATH" lake build Book
```

If method A uses the same solver environment as method B, replace `/opt/method-a-solver/bin` with `/opt/method-b-solver/bin`.

Do not skip these builds. The live survey can start Lean servers on demand, but prebuilding avoids very slow first-page interactions.

### 5. Configure The Survey Environment

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclidF
cp eval/survey/survey.env.example eval/survey/survey.env
nano eval/survey/survey.env
```

Set at least:

```bash
SURVEY_PUBLIC_URL=https://your-real-domain.example
SURVEY_EMAIL_FROM=your-gmail-address@gmail.com
SURVEY_SMTP_USERNAME=your-gmail-address@gmail.com
SURVEY_SMTP_PASSWORD=your-gmail-app-password
```

Set `SURVEY_ADMIN_PASSWORD` or `SURVEY_ADMIN_PASSWORD_HASH` in `survey.env` so the admin page can authenticate.

For Gmail, `SURVEY_SMTP_PASSWORD` must be a Gmail app password.

If solver binaries are not globally on `PATH`, set:

```bash
LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID=/opt/method-a-solver/bin
LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID_PLUS=/opt/method-b-solver/bin
```

### 6. Smoke-Test Locally

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclidF
eval/survey/launch_survey.sh
```

In another shell:

```bash
curl -I http://127.0.0.1:8765/
curl -I http://127.0.0.1:8765/admin/
```

Stop the foreground server with `Ctrl-C` after the smoke test.

### 7. Install systemd Service

Copy and edit the service file:

```bash
sudo cp /opt/lean-faithfulness-survey-hosting/deploy/lean-survey.service.example /etc/systemd/system/lean-survey.service
sudo nano /etc/systemd/system/lean-survey.service
```

Update `User=`, `WorkingDirectory=`, and `ExecStart=` if the repo path or VM username differs.

Then:

```bash
sudo systemctl daemon-reload
sudo systemctl enable lean-survey
sudo systemctl start lean-survey
sudo systemctl status lean-survey
```

Logs:

```bash
sudo journalctl -u lean-survey -n 100 --no-pager
```

### 8. Configure Caddy

Point DNS for the public domain to the VM IP address first.

Then:

```bash
sudo cp /opt/lean-faithfulness-survey-hosting/deploy/Caddyfile.example /etc/caddy/Caddyfile
sudo nano /etc/caddy/Caddyfile
sudo systemctl reload caddy
```

For IP-only HTTP testing, use this temporary Caddyfile instead:

```caddy
:80 {
    reverse_proxy 127.0.0.1:8765
}
```

### 9. Final Validation

Check:

```bash
curl -I http://127.0.0.1:8765/
curl -I https://your-real-domain.example/
sudo systemctl status lean-survey
```

Then open:

```text
https://your-real-domain.example/admin/
```

Use the admin password, create a reviewer code, return to the main page, and test one assigned proposition.

## Survey Runtime Files

Created at runtime and intentionally ignored:

```text
LeanEuclidF/eval/survey/survey.env
LeanEuclidF/eval/survey/data/responses.sqlite3
LeanEuclidF/eval/survey/data/reviewers.txt
LeanEuclidF/eval/survey/server.log
LeanEuclidF/eval/survey/server.pid
```

The admin password is configured through `LeanEuclidF/eval/survey/survey.env` or service environment variables and should not be committed.

## Current Survey Behavior

- Formalization names are anonymized as Formalization A and Formalization B.
- Reviewers are deterministically assigned 10 propositions by reviewer code.
- All 48 propositions are browsable, but only assigned propositions are reviewable.
- The four slow propositions are pinned for startup warm-up:
  - `book1_prop24`
  - `book1_prop43`
  - `book1_prop45`
  - `book1_prop47`
- Interactive Lean queries participate in the proposition cache policy.
- Admin memory stats show job/container memory, process-tree PSS, Lean PSS, and summed RSS.

## Useful Commands

Restart survey:

```bash
sudo systemctl restart lean-survey
```

Watch logs:

```bash
sudo journalctl -u lean-survey -f
```

Export responses:

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclidF
python3 eval/survey/export_responses.py
```

Rebuild survey data after changing Lean files or rubric:

```bash
cd /opt/lean-faithfulness-survey-hosting/LeanEuclidF
python3 eval/survey/extract_survey_data.py
```
