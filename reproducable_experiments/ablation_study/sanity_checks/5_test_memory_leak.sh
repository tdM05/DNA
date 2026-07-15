#!/usr/bin/env bash
set -uo pipefail
unset ANTHROPIC_API_KEY
cd "$(dirname "$0")"; mkdir -p out

# AUTH-SAFE: we only move the project memory dir aside. Auth is in a SEPARATE file
# (~/.claude/.credentials.json), never touched here — so no reauth risk.
MEMDIR="/u/taddmao/.claude/projects/-h-56-taddmao-code-autoform-DNA/memory"
HIDDEN="${MEMDIR}.HIDDEN_FOR_TEST"

# Always restore, even on crash/ctrl-c, so real memory is never left hidden.
# NOTE: Claude re-creates an empty memory/ dir when it finds none, so a plain
# `mv $HIDDEN $MEMDIR` would NEST the real dir inside it. Set aside anything that
# got recreated first, then move the real dir back.
restore() {
  if [ -d "$HIDDEN" ]; then
    [ -d "$MEMDIR" ] && mv "$MEMDIR" "${MEMDIR}.recreated_junk_$$"
    mv "$HIDDEN" "$MEMDIR" && echo "[memory restored]"
  fi
}
trap restore EXIT

PROBE='Without using any tools, tell me from memory/prior context ONLY: (1) anything you know about ME personally (mistakes I made, preferences, decisions from past sessions), and (2) past corrections/decisions in this proof project that are NOT in the current files. Be specific. If you recall nothing beyond the files in front of you, reply exactly: NOTHING_RECALLED'

echo "=== A) memory PRESENT — expect it to recall past-session/personal facts ==="
claude -p "$PROBE" --output-format json > out/mem_present.json
jq -r '.result' out/mem_present.json

echo
echo "=== B) memory HIDDEN (whole dir moved aside) — expect NOTHING_RECALLED / lost facts ==="
mv "$MEMDIR" "$HIDDEN"
claude -p "$PROBE" --output-format json > out/mem_hidden.json
jq -r '.result' out/mem_hidden.json
# trap restores on exit

echo
echo "=== verdict ==="
echo "If A recalls personal/past-session facts and B loses them (says NOTHING_RECALLED or"
echo "only cites the project CLAUDE.md), then hiding the memory dir cleanly severs memory —"
echo "auth untouched, no reauth. That's your naive-arm switch."
