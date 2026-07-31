# ⚠️ REBUILD Pistis.zip BEFORE SUBMIT — it is STALE

`tmp/Pistis.zip` predates recent edits. Rebuild it before uploading. **Delete this file before zipping.**

## Edits made AFTER the current tmp/Pistis.zip was built (must be in the next zip):
- `.claude/settings.json`: moved `safe_build.sh` from **allow → deny** (agent builds only via
  verification-wrapping tools; matches `main`). `lake build` already denied.
- `README.md`: added `pip install smt-portfolio` to step 1 (REQUIRED dispatcher the Lean SMT build
  invokes; without it the build errors `could not execute external process 'smt-portfolio'`). This
  was a real omission caught by a clean-machine build test.
- `README.md`: sharpened the intro to state clearly what's **turnkey** (build+check artifacts,
  regenerate plots) vs **reference-only** (running the Pistis agent pipeline live — needs Claude
  Code + model access + two-worktree harness; scripts included to read, not as a one-command rerun).
- **Deleted `requirements.txt`**; README step 3 rewritten to "no install needed" (plots are
  pre-rendered in the notebooks; re-running is optional matplotlib/numpy/pandas); `pyproject.toml`
  `dependencies = []`. Removes a failing/needless install step.
- `ablation_study/runner/README.md`: added a note that `result.txt` is the authoritative verdict
  (grade.log is a transient trace), and that a few runs were manually corrected for false automated
  results — with the Prop18 `lake`-not-found example.
  *(Also: skipped-prop `sorry` headers + `Book3/SKIPPED_PROPS.md`, README `Book`→`Book1` typo fix,
  `Book2/old/` dropped — these WERE in the last build; the safe_build fix was NOT.)*

## ⚠️ CRITICAL FIX for the rebuild — UNICODE FILENAMES
The previous zip DROPPED 6 unicode-named step files in Book3/Prop25 (haα₂.lean, haα₃, hbα₂, hbα₃,
hcα₂, hcα₃) because plain `git ls-files` OCTAL-ESCAPES non-ASCII names (`ha\316\261...`), and those
escaped paths fail `[ -e ]` → rsync skipped them → `Book3/Prop25/Main.lean` imports them → a
reviewer running `lake build Book3` gets `no such file: Book3/Prop25/haα₂.lean`.
FIX: build the ship list with **`git -c core.quotepath=false ls-files`** so unicode names come
through raw and pass `[ -e ]`. (24 such files total: 6 in Prop25 + 18 in kept transcript snapshots.)

## How to rebuild (same flow as before — stage, inject wired Bash hook into staged copy, zip):
```
# ship list: git-tracked (excl .lake) + human_eval (no pyc/DS_Store), existing on disk, minus notes
# NOTE the -c core.quotepath=false — REQUIRED so unicode filenames (Book3/Prop25/haα₂.lean etc.) are included
{ git -c core.quotepath=false ls-files | grep -v '/.lake/'; find reproducable_experiments/human_eval -type f | grep -vE '/\.lake/|__pycache__|\.pyc$|\.DS_Store'; } \
  | sort -u | grep -vE '^FINALIZE_BEFORE_ZIP.md$|^REBUILD_ZIP_TODO.md$' > /tmp/ship.txt
# keep only existing paths
while IFS= read -r f; do [ -e "$f" ] && printf '%s\n' "$f"; done < /tmp/ship.txt > /tmp/ship2.txt; mv /tmp/ship2.txt /tmp/ship.txt
# SANITY after staging: the 6 Prop25 unicode files must be present —
#   ls /tmp/Pistis_build/Pistis/LeanEuclidF/Book3/Prop25/ha*.lean  (expect haα₂.lean, haα₃.lean, ...)
rm -rf /tmp/Pistis_build; mkdir -p /tmp/Pistis_build/Pistis
rsync -aq --files-from=/tmp/ship.txt . /tmp/Pistis_build/Pistis/
# inject WIRED settings.json (Bash+Write+Edit hooks) into the STAGED copy only:
#   add {"matcher":"Bash","hooks":[{command: bash_hygiene.py}]} as first PreToolUse entry
# then: cd /tmp/Pistis_build && zip -qrX /tmp/Pistis.zip Pistis ; cp to tmp/Pistis.zip
```

## Audit the extracted zip (all must pass): 0 .git, 0 .lake, 0 __pycache__, 0 FINALIZE/REBUILD notes,
## 0 personal tokens (taddmao/liby99/tzhong4/tdM05/paths), 0 DNA (non-transcript), 0 LeanEuclidPlus;
## shipped settings hooks = [Bash, Write, Edit], safe_build+lake build in DENY, hygiene.conf = deny.

## Local-tree caveat (your machine, NOT the zip):
- `.claude/settings.json` on disk has the **Bash hook UNWIRED** (so the authoring shell worked).
  The zip gets it wired via staging injection. Re-wire locally if you want it active for your runs.
- `paper/` LeanEuclidPlus→LeanEuclidF edits need syncing to Overleaf + recompile.
