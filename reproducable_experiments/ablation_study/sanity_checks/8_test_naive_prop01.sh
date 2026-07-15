#!/usr/bin/env bash
# Does a NAIVE LLM (all methodology ablated) fill Book1/Prop01?
# Same harness as 6_test, with TWO differences:
#   (1) a blank-slate prompt (no pipeline/skill jargon), and
#   (2) the project auto-memory is HIDDEN so the agent gets zero recalled methodology facts.
# Usage: bash 8_test_naive_prop01.sh [BUDGET_USD] [MODEL]   (defaults 50, opus)
set -uo pipefail
unset ANTHROPIC_API_KEY                       # subscription auth
set +u; source "$HOME/.venvs/leaneuclid/bin/activate"; set -u  # z3/cvc5 on PATH for the agent's `lake build` (+u guards the activate script)

# Derive repo root from THIS script's location, real path (so the project SLUG matches
# what Claude uses for memory/session, regardless of cluster symlinks).
REPO="$(cd "$(dirname "$0")/../.." && pwd -P)"
OUT="$REPO/reproducable_experiments/ablation_study/out"
SLUG="$(echo "$REPO" | sed 's#/#-#g')"        # e.g. -h-56-taddmao-code-autoform-DNA
MEMDIR="$HOME/.claude/projects/${SLUG}/memory"
HIDDEN="${MEMDIR}.HIDDEN_naive"
mkdir -p "$OUT"

# --- hide auto-memory so the naive agent has NO cross-session facts -----------------
# Hardened restore (Claude recreates an empty memory/ when it finds none → set it aside first).
restore_mem() {
  if [ -d "$HIDDEN" ]; then
    [ -d "$MEMDIR" ] && mv "$MEMDIR" "${MEMDIR}.recreated_junk_$$"
    mv "$HIDDEN" "$MEMDIR" && echo "[memory restored]"
  fi
}
trap restore_mem EXIT
if [ -d "$MEMDIR" ]; then
  mv "$MEMDIR" "$HIDDEN" && echo "[memory hidden for naive run: $MEMDIR]"
else
  echo "!!!!!! WARNING: memory dir NOT found at $MEMDIR — memory is NOT hidden."
  echo "!!!!!! The naive agent may load recalled facts. Fix SLUG/path before trusting this run."
  echo "!!!!!! (Aborting to be safe.)"; exit 1
fi

cd "$REPO"

BUDGET="${1:-50.00}"
MODEL="${2:-opus}"
CERT='Prop01 of Book1 that I was assigned to work on, is completely done. I certify it is faithful, compiles with no sorry, and is ready for review.'

# NAIVE prompt: no mention of the pipeline, skills, check_step, or wiring. Just the task.
PROMPT="Book1/Prop01/Main.lean (under LeanEuclidPlus/) is a Lean proof of Euclid's Book 1 Proposition 1, with every step body left as ':= by sorry'. Fill in all the sorries so the file compiles and builds with NO sorry, making sure to cite any proposition Euclid cites (a proposition of the same number, or a variant of it, is fine). Do NOT use git. When it fully compiles with zero sorry, print on its OWN line EXACTLY this and nothing appended: ${CERT}"

CONT="Continue until Book1/Prop01/Main.lean compiles with zero sorry. Do NOT use git. Only when fully done, print on its own line EXACTLY: ${CERT}"

spent=0
remaining="$BUDGET"

call() { # $1 = prompt, $2 = extra args (for --resume)
  # naive settings.json allows everything except git; acceptEdits auto-approves file edits.
  # NO turn cap — the budget ($remaining) is the sole limit.
  claude -p "$1" $2 --model "$MODEL" --permission-mode acceptEdits --output-format json \
    --max-budget-usd "$remaining"
}

echo "=== turn 0: NAIVE headless fill of Book1/Prop01 (model=$MODEL, budget \$$BUDGET, memory hidden) ==="
out=$(call "$PROMPT" "")
echo "$out" > "$OUT/naive_prop01_turn0.json"
sid=$(echo "$out" | jq -r '.session_id')
JSONL=$(find "$HOME/.claude/projects" -name "$sid.jsonl" 2>/dev/null | head -1)
printf 'session_id: %s\ntranscript:  %s\n' "$sid" "${JSONL:-<pending>}" > "$OUT/naive_prop01_session.txt"
echo "session id + transcript path -> $OUT/naive_prop01_session.txt"

report() {
  local turncost; turncost=$(echo "$out" | jq -r '.total_cost_usd // 0')
  spent=$(awk "BEGIN{print $spent + $turncost}")
  remaining=$(awk "BEGIN{print $BUDGET - $spent}")
  echo "  cost=$turncost  cumulative=$spent  remaining=$remaining  subtype=$(echo "$out" | jq -r '.subtype')"
  echo "$out" | jq -r '.result' | tail -3
}
report

i=0
while true; do
  if echo "$out" | jq -r '.result' | grep -qF "$CERT"; then
    echo "=== ✅ CERTIFIED DONE (cumulative ~\$$spent). Naive agent finished. ==="; break
  fi
  if [ "$(echo "$out" | jq -r '.subtype')" = "error_max_budget_usd" ] || \
     [ "$(awk "BEGIN{print ($remaining <= 0.05)}")" = "1" ]; then
    echo "=== ⛔ BUDGET EXHAUSTED at ~\$$spent — recorded as NOT done ==="; break
  fi
  i=$((i+1))
  if [ "$i" -gt 200 ]; then echo "=== ⚠ safety backstop (200 rounds) hit ==="; break; fi
  echo "--- round $i: continue (remaining \$$remaining) ---"
  out=$(call "$CONT" "--resume $sid")
  echo "$out" > "$OUT/naive_prop01_turn$i.json"
  report
done

echo
echo "=== EVAL / grade (method-agnostic — IDENTICAL to the full arm) ==="
cd "$REPO/LeanEuclidPlus"
echo "files in prop dir:"; ls Book1/Prop01/*.lean 2>/dev/null
srr=$(grep -c 'sorry' Book1/Prop01/Main.lean 2>/dev/null)
echo "sorry count in Main (want 0): $srr"
echo; echo "+ python3 scripts/check_faithful.py Book1/Prop01/Main.lean"
python3 scripts/check_faithful.py Book1/Prop01/Main.lean
faith_rc=$?
echo "check_faithful exit code: $faith_rc"
if [ "${srr:-1}" = "0" ] && [ "$faith_rc" -eq 0 ]; then
  echo "=== ✅ GRADE: PASS — zero sorry, faithful. Naive arm succeeded. ==="
else
  echo "=== ❌ GRADE: FAIL — sorry left, faithfulness failed, or budget-cut. ==="
fi
# trap restores the hidden memory on exit (normal, error, or Ctrl-C)
