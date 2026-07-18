#!/usr/bin/env bash
# =============================================================================
# 7_view_transcript.sh — view a run's full transcript in the NORMAL Claude Code UI
# =============================================================================
#
# USAGE:
#   bash reproducable_experiments/ablation_study/7_view_transcript.sh
#       -> opens the LAST run's session (session id read from out/prop01_session.txt)
#
#   bash reproducable_experiments/ablation_study/7_view_transcript.sh <session-id>
#       -> opens a specific session by id
#
# WHAT IT DOES:
#   Runs `claude --resume <session-id>` from the repo root, which loads the whole
#   conversation into the native Claude Code TUI so you can scroll through every
#   turn exactly as it's normally rendered.
#
# HOW TO READ IT (it opens INTERACTIVELY):
#   - Scroll up/down to read the full history.
#   - When done, press Ctrl-C  (or type /exit) to leave.
#   - !! Do NOT type a prompt and press enter -- that CONTINUES the agent and
#        spends budget. This is for READING only.
#
# ALTERNATIVE (non-interactive plain-text dump, zero risk of continuing the agent):
#   f=$(grep '^transcript:' reproducable_experiments/ablation_study/out/prop01_session.txt | awk '{print $2}')
#   jq -rc 'if .type=="assistant" then (.message.content[]? | if .type=="text" then "\n[assistant] "+.text elif .type=="tool_use" then "[tool] "+.name+"  "+((.input|tostring)[0:220]) else empty end) elif .type=="user" then (.message.content[]? | if (type=="object" and .type=="tool_result") then "  -> "+((.content|tostring)[0:300]) else empty end) else empty end' "$f" | less -R
# =============================================================================
set -uo pipefail
cd "$(dirname "$0")"

SID="${1:-$(grep '^session_id:' out/prop01_session.txt | awk '{print $2}')}"
if [ -z "${SID:-}" ]; then echo "no session id (pass one as \$1, or run 6_test_fullmethod_prop01.sh first)"; exit 1; fi

echo "Opening session $SID in the Claude Code UI."
echo "READ-ONLY: scroll to read, then Ctrl-C or /exit. Do NOT type a prompt (that continues the agent)."
cd /h/56/taddmao/code/autoform/DNA        # --resume finds the session under this project
claude --resume "$SID"
