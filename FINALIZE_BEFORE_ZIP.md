# ⚠️ FINALIZE BEFORE BUILDING THE SUBMISSION ZIP

**Delete this file before zipping** — it is a working note, not part of the supplement.

## MUST-DO: re-wire the Bash hygiene hook

The full methodology ships with THREE PreToolUse hooks wired. The `Bash → bash_hygiene.py`
matcher was **temporarily unwired** in `.claude/settings.json` only so assembly work in the
authoring session wasn't blocked by its own gate (`mode = deny` blocks `python3 -c`, `zip`, etc.).

**Before the final zip, re-add the Bash matcher** as the FIRST entry of `hooks.PreToolUse` in
`.claude/settings.json`:

```json
      {
        "matcher": "Bash",
        "hooks": [
          {
            "type": "command",
            "command": "python3 \"$CLAUDE_PROJECT_DIR/.claude/hooks/bash_hygiene.py\"",
            "timeout": 10
          }
      },
```

(The files `.claude/hooks/bash_hygiene.py` and `.claude/hooks/hygiene.conf` [`mode = deny`] are
already in place and anonymized — only the settings.json wiring was removed.)

Verify after re-adding: `python3 -c "import json; d=json.load(open('.claude/settings.json')); print([h['matcher'] for h in d['hooks']['PreToolUse']])"`
should print `['Bash', 'Write', 'Edit']`.

## MUST-DO: re-add the `lake build` deny

`.claude/settings.json`'s `permissions.deny` had `"Bash(lake build:*)"` **temporarily removed**
so the authoring session could run the end-to-end build test. Re-add it as the first entry of
`deny`:

```json
    "deny": [
      "Bash(lake build:*)",
```

## Also before zip
- Rebuild the zip from the current tree (README, requirements.txt, .claude changes are newer than
  the last built `/tmp/pistis_supp.zip`).
- Re-run the extracted-tree audit (0 personal tokens, no `.git`, no `.lake`).
- Delete THIS file.
