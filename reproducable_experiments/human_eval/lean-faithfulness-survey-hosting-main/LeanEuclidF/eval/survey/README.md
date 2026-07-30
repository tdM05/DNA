# Faithfulness Survey App

This directory contains a data-driven reviewer interface for comparing Euclid formalizations against the faithfulness rubric in `../faithfulness_rubric.md`.

## Generate Survey Data

Run this from `LeanEuclidF` whenever textbook proofs, diagrams, LeanEuclid files, or new-method files change:

```bash
python3 eval/survey/extract_survey_data.py
```

Optional environment variables:

```bash
LEANEUCLID_ROOT=/path/to/LeanEuclid NEW_METHOD_LABEL="Your Method Name" python3 eval/survey/extract_survey_data.py
```

`LEANEUCLID_ROOT` may be absolute, or relative to the workspace root containing `LeanEuclidF`.

The extractor writes `eval/survey/data/survey_data.json`. It scans all Book I textbook proof files, all available LeanEuclid proposition files, diagrams, and any available new-method proposition directories such as `Book1/Prop06`.

## Lean-Line To Textbook-Sentence Mappings

Optional mapping files live in `eval/survey/line_sentence_mappings/`. The extractor reads files such as `book1_prop06.json`, validates sentence IDs against the proposition text, and writes normalized `line_text_mappings` into `survey_data.json`.

Use `eval/survey/line_sentence_mappings/README.md` as the standard prompt/specification for Codex, Claude Code, or human-created mappings. The website displays these mappings as small sentence badges beside Lean lines; hovering a badge shows the mapped textbook sentence(s), code ranges, and rationale.

Run the mapping pipeline with one command:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 6
```

That command writes a context file, writes a deterministic LLM prompt, validates `eval/survey/line_sentence_mappings/book1_prop06.json` if it exists, and regenerates `survey_data.json`. To ask an installed agent to create the mapping file in the same command:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 7 --agent codex
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 7 --agent claude
```

Run every available proposition in one command:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --all --agent codex
```

Existing mapping files are skipped by default. Use `--overwrite` only when you intentionally want to regenerate existing mappings:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --all --agent codex --overwrite
```

For a smaller batch:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --props 1,3,7-10 --agent codex
```

For another command-line agent, pass a command that reads the prompt on stdin and returns JSON on stdout:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 7 --agent-cmd "your-agent-command"
```

## Prepare Lean Projects

The survey can display source files without building both Lean projects, but live tactic states require each underlying Lake project to initialize successfully.

For `LeanEuclidF`:

```bash
cd /home/user2/Pistis/LeanEuclidF
lake exe cache get
lake build Book1.Prop06.Main
```

For `LeanEuclid`:

```bash
cd /home/user2/LeanEuclid
lake exe cache get
lake build Book.Prop06
```

Run these on a compute node with network access. If `lake env lean` or the survey shows a Git/GitHub error, the project dependencies are not ready yet.

## Run The Server

Before reviewers can enter the survey, register their assigned reviewer codes. Use either a comma-separated environment variable:

```bash
SURVEY_REVIEWER_CODES=R01,R02,R03 python3 eval/survey/server.py --host 127.0.0.1 --port 8765
```

or create `eval/survey/data/reviewers.txt` with one reviewer code per line. Lines may include comments after `#`; see `eval/survey/data/reviewers.example.txt` for the format.

Run the server on a compute node, not a login node, especially if reviewers will click Lean lines:

```bash
cd /home/user2/Pistis/LeanEuclidF
python3 eval/survey/server.py --host 127.0.0.1 --port 8765
```

Then open:

```text
http://127.0.0.1:8765
```

## Admin Page

The admin page is available at:

```text
http://127.0.0.1:8765/admin/
```

Admin login is separate from reviewer codes. Configure it with an environment variable before starting the server:

```bash
SURVEY_ADMIN_PASSWORD='replace-with-a-private-password' python3 eval/survey/server.py --host 127.0.0.1 --port 8765
```

For a hashed secret, store the SHA-256 digest instead:

```bash
SURVEY_ADMIN_PASSWORD_HASH='sha256:<hex-digest>' python3 eval/survey/server.py --host 127.0.0.1 --port 8765
```

If a local, untracked `eval/survey/data/admin_password.sha256` exists, the server reads that hash file automatically, so no admin-password environment variable is needed across launches. The hash file should contain one line:

```text
sha256:<hex-digest>
```

That local hash file is ignored by Git.

The admin page can add or disable reviewer codes, monitor reviewer and proposition progress, export saved responses, inspect survey-data health, and clear/cancel server-owned Lean warm-up state. It does not edit submitted scores or notes.

The admin page can also generate a random reviewer code and email the reviewer a short guide. Email delivery uses either SMTP or a local `sendmail` binary. Example SMTP configuration:

```bash
SURVEY_PUBLIC_URL='https://your-survey-url.example'
SURVEY_EMAIL_FROM='Faithfulness Survey <survey@example.edu>'
SURVEY_SMTP_HOST='smtp.example.edu'
SURVEY_SMTP_PORT=587
SURVEY_SMTP_TLS=1
SURVEY_SMTP_USERNAME='survey@example.edu'
SURVEY_SMTP_PASSWORD='private-password'
python3 eval/survey/server.py --host 127.0.0.1 --port 8765
```

If SMTP is not configured, the server tries `SURVEY_SENDMAIL`, `/usr/sbin/sendmail`, then `/usr/lib/sendmail`. The generated code is only kept in the reviewer table if email sending succeeds.

If the server is running on a remote compute node, connect with an SSH tunnel from your local machine:

```bash
ssh -L 8765:127.0.0.1:8765 <compute-node-host>
```

Then open `http://127.0.0.1:8765` locally.

## Reviewer Workflow

Reviewers enter an assigned reviewer code. The app persists scores centrally in SQLite, keyed by reviewer code, proposition, method, and metric. Each metric is scored independently for each available formalization. Notes are optional.

The proposition list marks propositions as:

- `Ready`: both LeanEuclid and the new method are available.
- `Missing pair`: LeanEuclid exists but the new method is not available yet, so scoring is disabled.
- `Done`: the reviewer has saved all metric scores for both methods.

## Lean Line Inspection

Clicking a Lean line calls `POST /api/lean/state`. The current implementation runs:

```bash
lake env lean --server
```

and uses Lean's LSP/RPC endpoint `Lean.Widget.getInteractiveGoals` to retrieve the tactic state at the selected line. If RPC fails, it falls back to:

```bash
lake env lean --json <file>
```

and returns nearby source context plus diagnostics.

The frontend also calls `POST /api/lean/warm` when a proposition is opened. Warm-up keeps a Lean server and elaborated file session alive for each visible formalization. The first warm-up can take several seconds because Lean must process the file; after that, line clicks should usually be small RPC calls and return close to instantly.

Relevant environment variable:

```bash
LEAN_SURVEY_TIMEOUT=25
LEAN_SURVEY_RPC_TIMEOUT=30
LEAN_SURVEY_CLICK_TIMEOUT=6
LEAN_SURVEY_DISABLE_RPC=1
LEAN_SURVEY_PATH_EXTENSIONS=/home/user2/.conda/envs/dna/bin:/home/user2/.elan/bin
LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID=/path/to/method-a/bin
LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID_PLUS=/path/to/method-b/bin
```

Use a larger timeout only on a compute node.

The server automatically prepends `~/.conda/envs/dna/bin` and `~/.elan/bin` to the PATH it gives Lean. This is needed because some files call `smt-portfolio`; if that binary is not on the backend PATH, Lean reports `could not execute external process 'smt-portfolio'`. The method-specific `LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID*` variables are only needed when the two formalizations require different solver binaries. Relative entries in these PATH extension variables are resolved against the corresponding Lean project root; absolute entries are used as-is.

Keep `eval/survey/survey.env` minimal for deployment: include only values that are active for that deployment. Optional path overrides such as `LEAN_SURVEY_PATH_EXTENSIONS*` should be omitted unless the VM actually needs custom solver locations.

## Response Storage And Export

By default, responses are stored in:

```text
eval/survey/data/responses.sqlite3
```

Override this location with:

```bash
SURVEY_DB=/path/to/responses.sqlite3 python3 eval/survey/server.py --host 127.0.0.1 --port 8765
```

`SURVEY_DB`, `SURVEY_REVIEWERS`, and `SURVEY_ADMIN_PASSWORD_HASH_FILE` may be absolute, or relative to `eval/survey/`.

Export all responses as JSON:

```bash
python3 eval/survey/export_responses.py --format json --out eval/survey/exports/responses.json
```

Export metric scores as CSV:

```bash
python3 eval/survey/export_responses.py --format csv --table responses --out eval/survey/exports/responses.csv
```

Export proposition-level notes as CSV:

```bash
python3 eval/survey/export_responses.py --format csv --table overall_notes --out eval/survey/exports/overall_notes.csv
```
