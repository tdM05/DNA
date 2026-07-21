#!/usr/bin/env bash
# =============================================================================
# view_transcript.sh — READ-ONLY viewer for ablation-study run transcripts
# =============================================================================
#
# This is a *viewing only* tool. Unlike the old version it does NOT run
# `claude --resume` (which opens the run INTERACTIVELY and can continue the
# agent / spend budget). It just parses a run's transcript.jsonl and pages it,
# so there is zero risk of accidentally resuming a stalled run.
#
# USAGE:
#   bash view_transcript.sh
#       -> interactive picker: lists every run under out/ and lets you choose one.
#
#   bash view_transcript.sh <n>
#       -> open run number <n> from the picker list.
#
#   bash view_transcript.sh <path>
#       -> a session dir, a transcript.jsonl, or a dir containing one.
#
#   bash view_transcript.sh <session-id>
#       -> the run whose transcript is <session-id>.jsonl under out/.
#
# Inside the pager: ↑/↓ PgUp/PgDn to scroll, `/` to search, `q` to quit.
# =============================================================================
set -uo pipefail
exec python3 "$(dirname "$0")/view_transcript.py" "$@"
