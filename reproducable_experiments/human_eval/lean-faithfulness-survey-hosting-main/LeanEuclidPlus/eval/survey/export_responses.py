#!/usr/bin/env python3
"""Export faithfulness survey responses from SQLite.

Examples:
    python3 export_responses.py --format json --out responses.json
    python3 export_responses.py --format csv --table responses --out responses.csv
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import sqlite3
import sys
import time
from pathlib import Path
from typing import Any


SURVEY_DIR = Path(__file__).resolve().parent
DB_PATH = Path(os.environ.get("SURVEY_DB", SURVEY_DIR / "data" / "responses.sqlite3"))


def now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def rows_as_dicts(db: sqlite3.Connection, table: str) -> list[dict[str, Any]]:
    db.row_factory = sqlite3.Row
    return [dict(row) for row in db.execute(f"SELECT * FROM {table} ORDER BY reviewer_code, proposition_id")]


def export_json(db_path: Path) -> dict[str, Any]:
    with sqlite3.connect(db_path) as db:
        return {
            "exported_at": now_iso(),
            "db_path": str(db_path),
            "responses": rows_as_dicts(db, "responses"),
            "overall_notes": rows_as_dicts(db, "overall_notes"),
        }


def export_csv(db_path: Path, table: str, out) -> None:
    with sqlite3.connect(db_path) as db:
        rows = rows_as_dicts(db, table)
    if rows:
        fieldnames = list(rows[0].keys())
    elif table == "responses":
        fieldnames = ["reviewer_code", "proposition_id", "method_id", "metric_id", "score", "note", "updated_at"]
    else:
        fieldnames = ["reviewer_code", "proposition_id", "note", "updated_at"]
    writer = csv.DictWriter(out, fieldnames=fieldnames)
    writer.writeheader()
    writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--db", type=Path, default=DB_PATH, help="SQLite response database path")
    parser.add_argument("--format", choices=["json", "csv"], default="json")
    parser.add_argument("--table", choices=["responses", "overall_notes"], default="responses", help="CSV table to export")
    parser.add_argument("--out", type=Path, help="Output file. Defaults to stdout.")
    args = parser.parse_args()

    if not args.db.exists():
        parser.error(f"database does not exist: {args.db}")

    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        with args.out.open("w", encoding="utf-8", newline="") as out:
            if args.format == "json":
                json.dump(export_json(args.db), out, ensure_ascii=False, indent=2)
                out.write("\n")
            else:
                export_csv(args.db, args.table, out)
    else:
        if args.format == "json":
            json.dump(export_json(args.db), sys.stdout, ensure_ascii=False, indent=2)
            sys.stdout.write("\n")
        else:
            export_csv(args.db, args.table, sys.stdout)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
