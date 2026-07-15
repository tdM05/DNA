#!/usr/bin/env bash
set -uo pipefail
unset ANTHROPIC_API_KEY                 # force subscription auth (API key would override + bill API)
cd "$(dirname "$0")"; mkdir -p out

claude -p "Reply with a one-sentence hello, then on its own line print exactly: ABLATION_DONE" \
  --output-format json \
  --max-budget-usd 0.50 \
  > out/headless.json

echo "--- result ---"
jq -r '.result' out/headless.json
echo "--- cost/usage/session ---"
jq '{cost: .total_cost_usd, in: .usage.input_tokens, out: .usage.output_tokens, session: .session_id}' out/headless.json
