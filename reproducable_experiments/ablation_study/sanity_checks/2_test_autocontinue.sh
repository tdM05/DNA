#!/usr/bin/env bash
set -uo pipefail
unset ANTHROPIC_API_KEY
cd "$(dirname "$0")"; mkdir -p out

# Prompt engineered to STOP EARLY on purpose, so we exercise auto-continue.
PROMPT='Count from 1 to 5. Print ONLY ONE number per reply, then STOP and ask "Should I continue?" — do NOT print the next number in the same reply. Once you have printed 5, print on its own line exactly: ABLATION_DONE'

out=$(claude -p "$PROMPT" --output-format json --max-budget-usd 0.50)
sid=$(echo "$out" | jq -r '.session_id')
echo "$out" > out/continue_turn0.json
echo "turn 0: $(echo "$out" | jq -r '.result' | tr '\n' ' ')"

for i in $(seq 1 8); do
  if echo "$out" | jq -r '.result' | grep -q 'ABLATION_DONE'; then
    echo "COMPLETE (model finished after auto-continues)"; exit 0
  fi
  out=$(claude -p "continue" --resume "$sid" --output-format json --max-budget-usd 0.50)
  echo "$out" > out/continue_turn$i.json
  echo "turn $i: $(echo "$out" | jq -r '.result' | tr '\n' ' ')"
done
echo "STOPPED: hit turn cap without ABLATION_DONE (inspect out/continue_turn*.json)"
