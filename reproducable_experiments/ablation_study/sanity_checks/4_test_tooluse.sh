#!/usr/bin/env bash
set -uo pipefail
unset ANTHROPIC_API_KEY
cd "$(dirname "$0")"; mkdir -p out       # cwd is now .../ablation_study
SCRATCH="out/tooltest.txt"
rm -f "$SCRATCH"

# The real harness must EDIT files and RUN commands headless without hanging on a
# permission prompt. --permission-mode acceptEdits auto-accepts file edits; the
# repo's own settings/hooks still govern bash (git status is read-only/allowed).
echo "=== headless tool use under --permission-mode acceptEdits ==="
set +e
claude -p 'Do two things then finish. (1) Create the file out/tooltest.txt containing exactly one line: TOOLS_WORK. (2) Run the shell command `git status --short` and tell me how many lines it printed. When both are done, print on its own line: ABLATION_DONE' \
  --permission-mode acceptEdits \
  --output-format json \
  --max-budget-usd 1.00 \
  > out/tool.json
code=$?
set -e

echo "exit code: $code"
echo "--- result (tail) ---"; jq -r '.result' out/tool.json 2>/dev/null | tail -20
echo "--- turns / cost / error ---"
jq '{turns: .num_turns, cost: .total_cost_usd, is_error: .is_error, subtype: .subtype}' out/tool.json 2>/dev/null
echo "--- did the Write tool actually run (no hang)? ---"
if [ -f "$SCRATCH" ]; then echo "YES — file exists:"; cat "$SCRATCH"; else echo "NO — edit blocked or hung"; fi
