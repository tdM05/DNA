#!/usr/bin/env bash
# Does the FULL method work headless? Drive the faithful pipeline on the reset
# Book1/Prop01 (premapped, unproven) until the agent certifies it done.
# Usage: bash 6_test_fullmethod_prop01.sh [BUDGET_USD]   (default 50)
set -uo pipefail
unset ANTHROPIC_API_KEY                       # subscription auth

REPO=/h/56/taddmao/code/autoform/DNA
OUT="$REPO/reproducable_experiments/ablation_study/out"
mkdir -p "$OUT"
cd "$REPO"                                     # launch from the REPO ROOT so Claude loads
                                              # .claude/settings.json (allow rules for check_step /
                                              # wire_main / Book1 edits) + hooks + CLAUDE.md + real
                                              # memory. (Launching from LeanEuclidPlus set project=
                                              # LeanEuclidPlus, so none of that loaded → denials.)

BUDGET="${1:-50.00}"                           # global cap across all turns
MODEL="${2:-opus}"                             # pin the model (alias or full id, e.g. claude-opus-4-8)
CERT='Prop01 of Book1 that I was assigned to work on, is completely done. I certify it is faithful, compiles with no sorry, and is ready for review.'

PROMPT="Book1/Prop01 (Euclid I.1) has been reset to a premapped-but-UNPROVEN state: LeanEuclidPlus/Book1/Prop01/Main.lean holds the faithful euclid_sentence map with every body ':= by sorry', and all backing stepN.lean files were deleted. The pipeline scripts live in LeanEuclidPlus/scripts, so cd into LeanEuclidPlus and run them from there (e.g. 'python3 scripts/check_step.py Book1/Prop01 ...'). Fully prove AND WIRE it using the faithful pipeline (your prove-euclid / faithful-prove skills). You know the process — get it done end to end so Main compiles with NO sorry. Do NOT use git. When Book1/Prop01 is completely done and wired, print on its OWN line EXACTLY this and nothing appended: ${CERT}"

CONT="Continue until Book1/Prop01 is completely proven AND wired (Main compiles, zero sorry). Do NOT use git. Only when fully done, print on its own line EXACTLY: ${CERT}"

spent=0
remaining="$BUDGET"

call() { # $1 = prompt, $2 = extra args (for --resume)
  # acceptEdits auto-approves file edits; the pipeline commands (check_step / wire_main) are
  # auto-approved by .claude/settings.json's allow list — which loads now that we launch from
  # the repo root. NO turn cap — the budget ($remaining) is the sole limit.
  claude -p "$1" $2 --model "$MODEL" --permission-mode acceptEdits --output-format json \
    --max-budget-usd "$remaining"
}

echo "=== turn 0: full-method headless prove of Book1/Prop01 (model=$MODEL, global budget \$$BUDGET) ==="
out=$(call "$PROMPT" "")
echo "$out" > "$OUT/prop01_turn0.json"
sid=$(echo "$out" | jq -r '.session_id')
# Record where the full turn-by-turn transcript lives (Claude auto-writes it there; we just
# point to it rather than copy the growing file). This is the artifact locator.
JSONL=$(find "$HOME/.claude/projects" -name "$sid.jsonl" 2>/dev/null | head -1)
printf 'session_id: %s\ntranscript:  %s\n' "$sid" "${JSONL:-<pending>}" > "$OUT/prop01_session.txt"
echo "session id + transcript path -> $OUT/prop01_session.txt"

report() {
  local turncost; turncost=$(echo "$out" | jq -r '.total_cost_usd // 0')
  spent=$(awk "BEGIN{print $spent + $turncost}")
  remaining=$(awk "BEGIN{print $BUDGET - $spent}")
  echo "  cost=$turncost  cumulative=$spent  remaining=$remaining  subtype=$(echo "$out" | jq -r '.subtype')"
  echo "$out" | jq -r '.result' | tail -3
}
report

# Loop until CERTIFIED or BUDGET runs out — budget is the real terminator, not a
# round count. The 200 is just a runaway-safety backstop (raise it if ever hit).
i=0
while true; do
  if echo "$out" | jq -r '.result' | grep -qF "$CERT"; then
    echo "=== ✅ CERTIFIED DONE (cumulative ~\$$spent). The METHOD ran headless. ==="
    break
  fi
  if [ "$(echo "$out" | jq -r '.subtype')" = "error_max_budget_usd" ] || \
     [ "$(awk "BEGIN{print ($remaining <= 0.05)}")" = "1" ]; then
    echo "=== ⛔ BUDGET EXHAUSTED at ~\$$spent — recorded as NOT done ==="; break
  fi
  i=$((i+1))
  if [ "$i" -gt 200 ]; then echo "=== ⚠ safety backstop (200 rounds) hit — raise if legit ==="; break; fi
  echo "--- round $i: continue (remaining \$$remaining) ---"
  out=$(call "$CONT" "--resume $sid")
  echo "$out" > "$OUT/prop01_turn$i.json"
  report
done

echo
echo "=== EVAL / phase_c grade (method-agnostic — same check for full and baseline) ==="
cd "$REPO/LeanEuclidPlus"                       # eval scripts + Book1 paths resolve from here
echo "files in prop dir:"; ls Book1/Prop01/*.lean 2>/dev/null
srr=$(grep -c 'sorry' Book1/Prop01/Main.lean 2>/dev/null)
echo "sorry count in wired Main (want 0): $srr"

echo; echo "+ python3 scripts/check_faithful.py Book1/Prop01/Main.lean"
python3 scripts/check_faithful.py Book1/Prop01/Main.lean
faith_rc=$?
echo "check_faithful exit code: $faith_rc"

if [ "${srr:-1}" = "0" ] && [ "$faith_rc" -eq 0 ]; then
  echo "=== ✅ GRADE: PASS — wired, zero sorry, faithful. Method ran headless end-to-end. ==="
else
  echo "=== ❌ GRADE: not clean — sorry left, faithfulness failed, or budget-cut. Inspect above. ==="
fi
echo "(heavier authoritative gate, if you want it: scripts/check_faithful.sh Book1 — needs built oleans)"
