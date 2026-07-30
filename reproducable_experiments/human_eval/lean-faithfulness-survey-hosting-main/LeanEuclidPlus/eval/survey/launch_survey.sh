#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."

if [ -f eval/survey/survey.env ]; then
  set -a
  . eval/survey/survey.env
  set +a
fi

exec python3 eval/survey/server.py \
  --host "${SURVEY_HOST:-127.0.0.1}" \
  --port "${SURVEY_PORT:-8765}"
