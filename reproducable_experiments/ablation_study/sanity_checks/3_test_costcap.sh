#!/usr/bin/env bash
set -uo pipefail
unset ANTHROPIC_API_KEY
cd "$(dirname "$0")"; mkdir -p out

# One turn already costs ~$0.18 (see test 1), so a $0.05 budget is BELOW one turn.
# Goal: see HOW the cap surfaces — exit code + is_error/subtype — so the real
# harness loop can detect "budget cut" and break instead of sending 'continue'.
echo "=== budget 0.05 (below one-turn cost) — expect a cut/error ==="
set +e
out=$(claude -p "Write a detailed 400-word explanation of Euclid's Elements Book 1." \
  --output-format json --max-budget-usd 0.05 2>out/capA.err)
code=$?
set -e
echo "exit code: $code"
echo "$out" > out/capA.json
echo "--- stderr ---"; cat out/capA.err
echo "--- result json fields ---"
echo "$out" | jq '{cost: .total_cost_usd, is_error: .is_error, subtype: .subtype, type: .type}' 2>/dev/null \
  || { echo "(not valid JSON — raw first 400 chars:)"; echo "$out" | head -c 400; echo; }

echo
echo "=== cost accounting on --resume: is total_cost_usd per-turn or cumulative? ==="
echo "turn0 cost: $(jq -r '.total_cost_usd' out/continue_turn0.json 2>/dev/null)"
echo "turn5 cost: $(jq -r '.total_cost_usd' out/continue_turn5.json 2>/dev/null)"
echo "(if turn5 >> turn0 and roughly = sum of turns, it's CUMULATIVE; if similar, per-turn)"
