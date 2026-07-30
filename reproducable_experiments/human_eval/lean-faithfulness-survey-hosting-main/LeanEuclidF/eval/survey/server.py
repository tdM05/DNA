#!/usr/bin/env python3
"""Standard-library survey server.

Run from this directory:
    python3 server.py --host 127.0.0.1 --port 8765
"""

from __future__ import annotations

import argparse
import atexit
import csv
import hashlib
import hmac
import io
import json
import os
import queue
import re
import secrets
import signal
import smtplib
import sqlite3
import subprocess
import threading
import time
from datetime import datetime, timezone
from email.message import EmailMessage
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
from pathlib import Path
from urllib.parse import urlparse, unquote, quote, parse_qs


SURVEY_DIR = Path(__file__).resolve().parent
LEANEUCLID_PLUS = SURVEY_DIR.parents[1]
REPO_ROOT = LEANEUCLID_PLUS.parent
WORKSPACE_ROOT = REPO_ROOT


def env_path(name: str, default: Path, base: Path) -> Path:
    raw = os.environ.get(name)
    path = Path(raw) if raw else default
    return path if path.is_absolute() else (base / path).resolve()


LEANEUCLID_ROOT = env_path("LEANEUCLID_ROOT", REPO_ROOT / "LeanEuclid", REPO_ROOT)
LEANEUCLID_PLUS_ROOT = env_path("LEANEUCLID_PLUS_ROOT", LEANEUCLID_PLUS, REPO_ROOT)
WEB_DIR = SURVEY_DIR / "web"
DATA_PATH = SURVEY_DIR / "data" / "survey_data.json"
DB_PATH = env_path("SURVEY_DB", SURVEY_DIR / "data" / "responses.sqlite3", SURVEY_DIR)
REVIEWERS_PATH = env_path("SURVEY_REVIEWERS", SURVEY_DIR / "data" / "reviewers.txt", SURVEY_DIR)
ADMIN_PASSWORD_HASH_PATH = env_path("SURVEY_ADMIN_PASSWORD_HASH_FILE", SURVEY_DIR / "data" / "admin_password.sha256", SURVEY_DIR)
TUTORIAL_VERSION = "2"
REVIEWER_CODE_ALPHABET = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
SQLITE_BUSY_TIMEOUT_MS = int(os.environ.get("SURVEY_SQLITE_BUSY_TIMEOUT_MS", "5000"))
REVIEW_ASSIGNMENT_COUNT = int(os.environ.get("SURVEY_REVIEW_ASSIGNMENT_COUNT", "10"))
# Fixed review pool selected from the middle/light-middle burden band:
# exclude the shortest likely-trivial items and the longest/heaviest outliers.
REVIEW_ASSIGNMENT_POOL_PROP_IDS = (
    "book1_prop01",
    "book1_prop02",
    "book1_prop06",
    "book1_prop07",
    "book1_prop08",
    "book1_prop09",
    "book1_prop11",
    "book1_prop12",
    "book1_prop13",
    "book1_prop14",
    "book1_prop15",
    "book1_prop16",
    "book1_prop17",
    "book1_prop20",
    "book1_prop23",
    "book1_prop25",
    "book1_prop27",
    "book1_prop28",
    "book1_prop30",
    "book1_prop32",
    "book1_prop33",
    "book1_prop35",
    "book1_prop36",
    "book1_prop37",
    "book1_prop38",
    "book1_prop39",
    "book1_prop40",
    "book1_prop42",
    "book1_prop43",
    "book1_prop46",
)
REVIEW_ASSIGNMENT_EXTRA_PROP_IDS = {}

LEAN_SESSIONS: dict[tuple[str, str, str], "LeanFileSession"] = {}
LEAN_SESSION_INFLIGHT: dict[tuple[str, str, str], dict] = {}
LEAN_SESSIONS_LOCK = threading.Lock()
WARM_QUEUE: queue.Queue[dict] = queue.Queue()
WARM_LOCK = threading.Lock()
WARM_REQUESTS: dict[str, dict] = {}
WARM_LATEST_ID = 0
WARM_WORKERS_STARTED = False
WARM_WORKER_COUNT = int(os.environ.get("LEAN_SURVEY_WARM_CONCURRENCY", "2"))
LEAN_SESSION_INIT_CONCURRENCY = int(os.environ.get("LEAN_SURVEY_SESSION_INIT_CONCURRENCY", str(max(1, WARM_WORKER_COUNT))))
LEAN_SESSION_INIT_COND = threading.Condition()
LEAN_SESSION_INIT_ACTIVE = 0
LEAN_SESSION_INIT_WAITING_INTERACTIVE = 0
LEAN_SESSION_INIT_WAITING_BACKGROUND = 0
WARM_ACTIVE_CLIENTS: dict[str, set["LeanLspClient"]] = {}
WARM_SESSION_KEYS: dict[str, set[tuple[str, str, str]]] = {}
CLIENT_ACTIVE_PROP: dict[str, str] = {}
CLIENT_LATEST_WARM_ID: dict[str, str] = {}
WARM_INFLIGHT_BY_PROP: dict[str, str] = {}
PROP_ACTIVE_CLIENTS: dict[str, set["LeanLspClient"]] = {}
PROP_SESSION_KEYS: dict[str, set[tuple[str, str, str]]] = {}
PROP_CACHE_LRU: list[str] = []
PROP_CLIENT_CLAIMS: dict[str, set[str]] = {}
CLIENT_PROP_CLAIMS: dict[str, list[str]] = {}
PROP_CACHE_SIZE = int(os.environ.get("LEAN_SURVEY_PROP_CACHE_SIZE", "6"))
PROP_CLIENT_CLAIM_CAP = int(os.environ.get("LEAN_SURVEY_CLIENT_PROP_CLAIM_CAP", "3"))
PINNED_WARM_PROP_IDS = {
    item.strip()
    for item in os.environ.get("LEAN_SURVEY_PINNED_WARM_PROPS", "book1_prop24,book1_prop43,book1_prop45,book1_prop47").split(",")
    if item.strip()
}
LEAN_STATE_LATEST_ID = 0
LEAN_STATE_LATEST_BY_CLIENT_PROP: dict[tuple[str, str], int] = {}
LEAN_DIRECT_ENV_CACHE: dict[str, dict[str, str]] = {}
LEAN_DIRECT_ENV_LOCK = threading.Lock()
ADMIN_SESSIONS: dict[str, float] = {}
ADMIN_SESSIONS_LOCK = threading.Lock()
ADMIN_SESSION_SECONDS = int(os.environ.get("SURVEY_ADMIN_SESSION_SECONDS", "28800"))
INVITE_RATE_LOCK = threading.Lock()
INVITE_RATE_BY_IP: dict[str, list[float]] = {}
INVITE_RATE_WINDOW_SECONDS = int(os.environ.get("SURVEY_INVITE_RATE_WINDOW_SECONDS", "3600"))
INVITE_RATE_MAX_PER_IP = int(os.environ.get("SURVEY_INVITE_RATE_MAX_PER_IP", "20"))
INVITE_RESEND_COOLDOWN_SECONDS = int(os.environ.get("SURVEY_INVITE_RESEND_COOLDOWN_SECONDS", "60"))


def close_lean_sessions() -> None:
    with LEAN_SESSIONS_LOCK:
        sessions = list(LEAN_SESSIONS.values())
        LEAN_SESSIONS.clear()
    for session in sessions:
        session.close()


atexit.register(close_lean_sessions)


def handle_shutdown_signal(signum, frame) -> None:
    close_lean_sessions()
    raise SystemExit(128 + int(signum))


signal.signal(signal.SIGTERM, handle_shutdown_signal)
signal.signal(signal.SIGINT, handle_shutdown_signal)


def lean_toolchain_lib(root: Path) -> Path | None:
    toolchain_file = root / "lean-toolchain"
    if not toolchain_file.exists():
        return None
    toolchain = toolchain_file.read_text(encoding="utf-8").strip()
    if not toolchain:
        return None
    if ":" in toolchain:
        origin, version = toolchain.split(":", 1)
        toolchain_name = f"{origin.replace('/', '--')}---{version}"
    else:
        toolchain_name = toolchain.replace("/", "--")
    lib_dir = Path.home() / ".elan" / "toolchains" / toolchain_name / "lib" / "lean"
    return lib_dir if lib_dir.exists() else None


def lean_toolchain_bin(root: Path) -> Path | None:
    lib_dir = lean_toolchain_lib(root)
    if not lib_dir:
        return None
    bin_dir = lib_dir.parent.parent / "bin"
    return bin_dir if bin_dir.exists() else None


def absolutize_path_list(value: str, root: Path) -> str:
    parts = []
    for item in value.split(os.pathsep):
        if not item:
            continue
        path = Path(item)
        parts.append(str((root / path).resolve()) if not path.is_absolute() else item)
    return os.pathsep.join(parts)


def lake_build_lib_dirs(build_dir: Path) -> list[Path]:
    # Lean 4.8-era Lake projects place artifacts directly under build/lib.
    # Lean 4.19-era Lake projects place Lean artifacts under build/lib/lean.
    candidates = [build_dir / "lib", build_dir / "lib" / "lean"]
    return [p.resolve() for p in candidates if p.exists()]


def lean_env(root: Path) -> dict[str, str]:
    env = os.environ.copy()
    path_parts = []
    root_resolved = root.resolve()
    if root_resolved == LEANEUCLID_ROOT.resolve():
        configured = os.environ.get("LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID", "")
    elif root_resolved == LEANEUCLID_PLUS.resolve():
        configured = os.environ.get("LEAN_SURVEY_PATH_EXTENSIONS_LEANEUCLID_PLUS", "")
    else:
        configured = ""
    if configured:
        path_parts.extend(p for p in absolutize_path_list(configured, root).split(os.pathsep) if p)
    configured = os.environ.get("LEAN_SURVEY_PATH_EXTENSIONS", "")
    if configured:
        path_parts.extend(p for p in absolutize_path_list(configured, root).split(os.pathsep) if p)
    for default in (
        Path.home() / ".conda" / "envs" / "dna" / "bin",
        Path.home() / ".elan" / "bin",
    ):
        if default.exists():
            path_parts.append(str(default))
    path_parts.append(env.get("PATH", ""))
    env["PATH"] = os.pathsep.join(p for p in path_parts if p)
    ld_parts = []
    project_lib = lean_toolchain_lib(root)
    if project_lib:
        ld_parts.append(str(project_lib))
    ld_parts.append(env.get("LD_LIBRARY_PATH", ""))
    env["LD_LIBRARY_PATH"] = os.pathsep.join(p for p in ld_parts if p)
    return env


def lean_direct_env(root: Path) -> dict[str, str]:
    key = str(root.resolve())
    with LEAN_DIRECT_ENV_LOCK:
        cached = LEAN_DIRECT_ENV_CACHE.get(key)
        if cached is not None:
            return cached.copy()

    env = lean_env(root)
    packages_dir = root / ".lake" / "packages"
    package_names: list[str] = []
    manifest_path = root / "lake-manifest.json"
    if manifest_path.exists():
        try:
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
            package_names = [
                str(pkg.get("name"))
                for pkg in manifest.get("packages", [])
                if isinstance(pkg, dict) and pkg.get("name")
            ]
        except Exception:
            package_names = []
    if not package_names and packages_dir.exists():
        package_names = sorted(p.name for p in packages_dir.iterdir() if p.is_dir())

    lib_parts: list[str] = []
    bin_parts: list[str] = []
    for name in package_names:
        build_dir = packages_dir / name / ".lake" / "build"
        bin_dir = build_dir / "bin"
        for lib_dir in lake_build_lib_dirs(build_dir):
            lib_parts.append(str(lib_dir))
        if bin_dir.exists():
            bin_parts.append(str(bin_dir.resolve()))

    root_build = root / ".lake" / "build"
    root_bin = root_build / "bin"
    for lib_dir in lake_build_lib_dirs(root_build):
        lib_parts.append(str(lib_dir))
    toolchain_lib = lean_toolchain_lib(root)
    if toolchain_lib:
        lib_parts.append(str(toolchain_lib.resolve()))
    if root_bin.exists():
        bin_parts.append(str(root_bin.resolve()))
    toolchain_bin = lean_toolchain_bin(root)
    if toolchain_bin:
        bin_parts.append(str(toolchain_bin.resolve()))

    if lib_parts:
        env["LEAN_PATH"] = os.pathsep.join(lib_parts)
        existing_ld = env.get("LD_LIBRARY_PATH", "")
        env["LD_LIBRARY_PATH"] = os.pathsep.join([*lib_parts, existing_ld] if existing_ld else lib_parts)
    if bin_parts:
        env["PATH"] = os.pathsep.join([*bin_parts, env.get("PATH", "")])

    src_parts = [str(root.resolve())]
    if env.get("LEAN_SRC_PATH"):
        src_parts.append(env["LEAN_SRC_PATH"])
    env["LEAN_SRC_PATH"] = os.pathsep.join(src_parts)

    with LEAN_DIRECT_ENV_LOCK:
        LEAN_DIRECT_ENV_CACHE[key] = env.copy()
    return env


def lean_server_command(root: Path) -> list[str]:
    bin_dir = lean_toolchain_bin(root)
    lean = bin_dir / "lean" if bin_dir else Path("lean")
    return [str(lean), "--server"]


def descendant_pids(pid: int) -> list[int]:
    try:
        output = subprocess.check_output(
            ["ps", "-eo", "pid=,ppid="],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        return []
    children: dict[int, list[int]] = {}
    for line in output.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        child, parent = int(parts[0]), int(parts[1])
        children.setdefault(parent, []).append(child)
    found: list[int] = []
    stack = list(children.get(pid, []))
    while stack:
        child = stack.pop()
        found.append(child)
        stack.extend(children.get(child, []))
    return found


def file_uri(path: Path) -> str:
    return "file://" + quote(str(path.resolve()))


def path_from_file_uri(uri: str) -> Path | None:
    parsed = urlparse(uri)
    if parsed.scheme != "file":
        return None
    return Path(unquote(parsed.path)).resolve()


def is_relative_to(path: Path, root: Path) -> bool:
    try:
        path.resolve().relative_to(root.resolve())
        return True
    except ValueError:
        return False


def tagged_text_to_string(value) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, list):
        return "".join(tagged_text_to_string(v) for v in value)
    if not isinstance(value, dict):
        return ""
    if "text" in value:
        return str(value["text"])
    if "append" in value:
        return "".join(tagged_text_to_string(v) for v in value["append"])
    if "tag" in value and isinstance(value["tag"], list) and len(value["tag"]) >= 2:
        return tagged_text_to_string(value["tag"][1])
    return ""


def tagged_text_to_nodes(value, tags: list[dict] | None = None) -> list[dict]:
    tags = tags or []
    if isinstance(value, str):
        return [{"text": value, "tags": tags}] if value else []
    if isinstance(value, list):
        nodes = []
        for item in value:
            nodes.extend(tagged_text_to_nodes(item, tags))
        return nodes
    if not isinstance(value, dict):
        return []
    if "text" in value:
        text = str(value["text"])
        return [{"text": text, "tags": tags}] if text else []
    if "append" in value:
        nodes = []
        for item in value["append"]:
            nodes.extend(tagged_text_to_nodes(item, tags))
        return nodes
    if "tag" in value and isinstance(value["tag"], list) and len(value["tag"]) >= 2:
        tag = value["tag"][0] if isinstance(value["tag"][0], dict) else {"value": value["tag"][0]}
        return tagged_text_to_nodes(value["tag"][1], tags + [tag])
    return []


def lean_code_payload(value) -> dict:
    nodes = tagged_text_to_nodes(value)
    segments = []
    for node in nodes:
        info_ref = None
        subexpr_pos = ""
        for tag in reversed(node.get("tags") or []):
            if isinstance(tag, dict) and isinstance(tag.get("info"), dict):
                info_ref = tag["info"]
                subexpr_pos = str(tag.get("subexprPos", ""))
                break
        segments.append({
            "text": node.get("text", ""),
            "infoRef": info_ref,
            "subexprPos": subexpr_pos,
        })
    return {
        "text": tagged_text_to_string(value).strip(),
        "segments": segments,
    }


def rpc_ref(value) -> dict | None:
    if isinstance(value, dict) and isinstance(value.get("p"), str):
        return {"p": value["p"]}
    if isinstance(value, dict) and isinstance(value.get("__rpcref"), str):
        return {"__rpcref": value["__rpcref"]}
    return None


def trace_embed_payload(tag: dict) -> dict | None:
    raw = tag.get("trace")
    if raw is None:
        return None
    if isinstance(raw, list):
        indent = raw[0] if len(raw) > 0 else 0
        cls = raw[1] if len(raw) > 1 else ""
        msg = raw[2] if len(raw) > 2 else {}
        collapsed = raw[3] if len(raw) > 3 else False
        children = raw[4] if len(raw) > 4 else {}
    elif isinstance(raw, dict):
        indent = raw.get("indent", 0)
        cls = raw.get("cls", "")
        msg = raw.get("msg", {})
        collapsed = raw.get("collapsed", False)
        children = raw.get("children", {})
    else:
        return None

    mode = ""
    child_items = []
    child_ref = None
    if isinstance(children, dict):
        if "strict" in children:
            mode = "strict"
            child_items = children.get("strict") or []
        elif "lazy" in children:
            mode = "lazy"
            child_ref = rpc_ref(children.get("lazy")) or children.get("lazy")
        else:
            child_ref = rpc_ref(children)
            mode = "lazy" if child_ref else ""
    elif isinstance(children, list):
        mode = "strict"
        child_items = children

    return {
        "kind": "trace",
        "indent": indent,
        "class": str(cls),
        "collapsed": bool(collapsed),
        "header": interactive_message_payload(msg),
        "childrenMode": mode,
        "childrenRef": child_ref,
        "children": [interactive_message_payload(item) for item in child_items if isinstance(item, (dict, list, str))],
        "raw": tag,
    }


def interactive_message_payload(value) -> dict:
    parts = []

    def visit(node, inherited_tags=None):
        inherited_tags = inherited_tags or []
        if isinstance(node, str):
            if node:
                parts.append({"kind": "text", "text": node})
            return
        if isinstance(node, list):
            for item in node:
                visit(item, inherited_tags)
            return
        if not isinstance(node, dict):
            return
        if "text" in node:
            text = str(node["text"])
            if text:
                if inherited_tags:
                    parts.append({"kind": "code", "code": lean_code_payload({"tag": [inherited_tags[-1], {"text": text}]})})
                else:
                    parts.append({"kind": "text", "text": text})
            return
        if "append" in node:
            for item in node["append"]:
                visit(item, inherited_tags)
            return
        if "tag" in node and isinstance(node["tag"], list) and len(node["tag"]) >= 2:
            tag = node["tag"][0] if isinstance(node["tag"][0], dict) else {"value": node["tag"][0]}
            child = node["tag"][1]
            trace = trace_embed_payload(tag)
            if trace:
                parts.append(trace)
                return
            if "goal" in tag and isinstance(tag["goal"], dict):
                parts.append({"kind": "goal", "goal": normalize_goal(tag["goal"])})
                return
            if "expr" in tag:
                parts.append({"kind": "code", "code": lean_code_payload(tag["expr"])})
                return
            visit(child, inherited_tags + [tag])

    visit(value)
    return {
        "text": tagged_text_to_string(value).strip(),
        "parts": parts,
    }


def normalize_range(rng: dict | None) -> dict | None:
    if not isinstance(rng, dict):
        return None
    start = rng.get("start")
    end = rng.get("end")
    if not isinstance(start, dict) or not isinstance(end, dict):
        return None
    return {
        "start": {
            "line": int(start.get("line", 0)) + 1,
            "column": int(start.get("character", 0)),
        },
        "end": {
            "line": int(end.get("line", 0)) + 1,
            "column": int(end.get("character", 0)),
        },
    }


def severity_label(value) -> str:
    return {1: "error", 2: "warning", 3: "info", 4: "hint"}.get(value, "info")


def format_goal(goal: dict) -> str:
    lines = []
    name = goal.get("userName?") or goal.get("userName")
    if name:
        lines.append(f"case {name}")
    for hyp in goal.get("hyps", []):
        names = [n for n in hyp.get("names", []) if "[anonymous]" not in n]
        if not names:
            continue
        hyp_type = tagged_text_to_string(hyp.get("type", "")).strip()
        hyp_value = tagged_text_to_string(hyp.get("val?", "")).strip() if hyp.get("val?") else ""
        suffix = f" := {hyp_value}" if hyp_value else ""
        lines.append(f"{' '.join(names)} : {hyp_type}{suffix}")
    target = tagged_text_to_string(goal.get("type", "")).strip()
    lines.append(f"{goal.get('goalPrefix', '⊢ ')}{target}")
    return "\n".join(lines)


def format_goals(result: dict) -> str:
    goals = result.get("goals") or []
    if not goals:
        return "No goals."
    return "\n\n".join(format_goal(goal) for goal in goals)


def normalize_goal(goal: dict) -> dict:
    hyps = []
    for hyp in goal.get("hyps", []):
        names = [n for n in hyp.get("names", []) if "[anonymous]" not in n]
        if not names:
            continue
        hyps.append({
            "names": names,
            "type": tagged_text_to_string(hyp.get("type", "")).strip(),
            "typeCode": lean_code_payload(hyp.get("type", "")),
            "value": tagged_text_to_string(hyp.get("val?", "")).strip() if hyp.get("val?") else "",
            "valueCode": lean_code_payload(hyp.get("val?", "")) if hyp.get("val?") else None,
            "fvarIds": hyp.get("fvarIds", []),
            "isInstance": bool(hyp.get("isInstance?", False) or hyp.get("isInstanceImplicit", False)),
            "isType": bool(hyp.get("isType?", False) or hyp.get("isType", False)),
            "isInserted": bool(hyp.get("isInserted?", False)),
            "isRemoved": bool(hyp.get("isRemoved?", False)),
        })
    target = tagged_text_to_string(goal.get("type", "")).strip()
    return {
        "userName": goal.get("userName?", "") or goal.get("userName", ""),
        "mvarId": goal.get("mvarId", ""),
        "goalPrefix": goal.get("goalPrefix", "⊢ "),
        "isInserted": bool(goal.get("isInserted?", False) or goal.get("isInserted", False)),
        "isRemoved": bool(goal.get("isRemoved?", False)),
        "hyps": hyps,
        "target": target,
        "targetCode": lean_code_payload(goal.get("type", "")),
        "text": format_goal(goal),
    }


def normalize_goals(result: dict) -> list[dict]:
    return [normalize_goal(goal) for goal in result.get("goals") or []]


def normalize_term_goal(result: dict | None) -> dict | None:
    if not isinstance(result, dict):
        return None
    goal = normalize_goal(result)
    goal["range"] = normalize_range(result.get("range"))
    goal["term"] = result.get("term")
    return goal


def normalize_interactive_diagnostic(diag: dict) -> dict:
    rng = normalize_range(diag.get("range"))
    start = (rng or {}).get("start", {})
    return {
        "severity": severity_label(diag.get("severity")),
        "line": start.get("line", 0),
        "column": start.get("column", 0),
        "message": tagged_text_to_string(diag.get("message", "")).strip(),
        "messageCode": lean_code_payload(diag.get("message", "")),
        "messageTree": interactive_message_payload(diag.get("message", "")),
        "range": rng,
        "source": diag.get("source?") or diag.get("source", "Lean 4"),
        "code": diag.get("code?") or diag.get("code", ""),
        "tags": diag.get("tags?") or diag.get("tags", []),
        "raw": diag,
    }


def normalize_lsp_diagnostic(diag: dict) -> dict:
    rng = normalize_range(diag.get("range"))
    start = (rng or {}).get("start", {})
    return {
        "severity": severity_label(diag.get("severity")),
        "line": start.get("line", 0),
        "column": start.get("column", 0),
        "message": diag.get("message", ""),
        "source": diag.get("source", ""),
        "code": diag.get("code", ""),
        "tags": diag.get("tags", []),
        "range": rng,
        "raw": diag,
    }


def lean_file_progress_complete(msg: dict, uri: str) -> bool:
    if msg.get("method") != "$/lean/fileProgress":
        return False
    params = msg.get("params", {})
    text_document = params.get("textDocument") or {}
    if text_document.get("uri") != uri:
        return False
    processing = params.get("processing") or []
    return not processing


def lean_file_progress_fatal(msg: dict, uri: str) -> bool:
    if msg.get("method") != "$/lean/fileProgress":
        return False
    params = msg.get("params", {})
    text_document = params.get("textDocument") or {}
    if text_document.get("uri") != uri:
        return False
    processing = params.get("processing") or []
    return any(isinstance(item, dict) and item.get("kind") == 2 for item in processing)


def hover_content_text(contents) -> str:
    if contents is None:
        return ""
    if isinstance(contents, str):
        return contents
    if isinstance(contents, list):
        return "\n\n".join(part for part in (hover_content_text(item) for item in contents) if part)
    if isinstance(contents, dict):
        value = contents.get("value")
        if value is not None:
            return str(value)
    return ""


def normalize_hover(result) -> dict:
    if not isinstance(result, dict):
        return {"text": "", "range": None, "raw": result}
    return {
        "text": hover_content_text(result.get("contents")).strip(),
        "range": normalize_range(result.get("range")),
        "raw": result,
    }


def normalize_lsp_location(value) -> dict | None:
    if not isinstance(value, dict):
        return None
    uri = value.get("targetUri") or value.get("uri")
    rng = value.get("targetSelectionRange") or value.get("targetRange") or value.get("range")
    path = path_from_file_uri(uri) if isinstance(uri, str) else None
    if not path:
        return None
    return {
        "uri": uri,
        "path": str(path),
        "range": normalize_range(rng),
    }


def normalize_lsp_locations(result) -> list[dict]:
    if result is None:
        return []
    items = result if isinstance(result, list) else [result]
    return [loc for loc in (normalize_lsp_location(item) for item in items) if loc]


def safe_source_roots(project_root: Path) -> list[Path]:
    roots = [project_root.resolve()]
    packages = project_root / ".lake" / "packages"
    if packages.exists():
        roots.append(packages.resolve())
    elan = Path.home() / ".elan" / "toolchains"
    if elan.exists():
        roots.append(elan.resolve())
    return roots


def resolve_project_root(root_value: str | Path) -> Path:
    root = Path(root_value).expanduser()
    if root.exists():
        return root.resolve()
    if root.name == "LeanEuclid":
        return LEANEUCLID_ROOT.resolve()
    if root.name == "LeanEuclidF":
        return LEANEUCLID_PLUS_ROOT.resolve()
    local = REPO_ROOT / root.name
    if local.exists():
        return local.resolve()
    return root.resolve()


def display_file_path(root: Path, file_path: Path) -> str:
    try:
        return file_path.relative_to(root).as_posix()
    except ValueError:
        return str(file_path)


def source_payload(path: Path, display_path: str | None = None) -> dict:
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    return {
        "path": display_path or str(path),
        "external": True,
        "lines": [
            {"line": i + 1, "text": text, "path": display_path or str(path)}
            for i, text in enumerate(lines)
        ],
    }


def normalize_info_popup(result) -> dict:
    if not isinstance(result, dict):
        return {"type": None, "exprExplicit": None, "doc": "", "raw": result}
    type_code = lean_code_payload(result.get("type")) if result.get("type") is not None else None
    explicit_code = lean_code_payload(result.get("exprExplicit")) if result.get("exprExplicit") is not None else None
    return {
        "type": type_code,
        "exprExplicit": explicit_code,
        "doc": str(result.get("doc") or ""),
        "raw": result,
    }


class LeanLspClient:
    def __init__(self, root: Path, warm_request_id: str | None = None, prop_id: str | None = None, client_id: str = "default"):
        self.warm_request_id = str(warm_request_id) if warm_request_id else ""
        self.prop_id = str(prop_id) if prop_id else ""
        self.client_id = lean_client_id(client_id)
        self.proc = subprocess.Popen(
            lean_server_command(root),
            cwd="/tmp",
            env=lean_direct_env(root),
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=False,
            start_new_session=True,
        )
        self.next_id = 1
        self.messages: queue.Queue[dict] = queue.Queue()
        self.stderr: queue.Queue[bytes] = queue.Queue()
        if self.warm_request_id:
            with WARM_LOCK:
                WARM_ACTIVE_CLIENTS.setdefault(self.warm_request_id, set()).add(self)
        if self.prop_id:
            with WARM_LOCK:
                PROP_ACTIVE_CLIENTS.setdefault(self.prop_id, set()).add(self)
        threading.Thread(target=self._read_stdout, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()

    def close(self) -> None:
        try:
            if self.proc.poll() is None:
                child_pids = descendant_pids(self.proc.pid)
                try:
                    for pid in child_pids:
                        try:
                            os.killpg(pid, signal.SIGTERM)
                        except ProcessLookupError:
                            try:
                                os.kill(pid, signal.SIGTERM)
                            except ProcessLookupError:
                                pass
                        except PermissionError:
                            try:
                                os.kill(pid, signal.SIGTERM)
                            except ProcessLookupError:
                                pass
                    os.killpg(self.proc.pid, signal.SIGTERM)
                    self.proc.wait(timeout=2)
                except Exception:
                    for pid in child_pids:
                        try:
                            os.killpg(pid, signal.SIGKILL)
                        except ProcessLookupError:
                            try:
                                os.kill(pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                        except PermissionError:
                            try:
                                os.kill(pid, signal.SIGKILL)
                            except ProcessLookupError:
                                pass
                    try:
                        os.killpg(self.proc.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    try:
                        self.proc.wait(timeout=2)
                    except Exception:
                        pass
        finally:
            if self.warm_request_id:
                with WARM_LOCK:
                    clients = WARM_ACTIVE_CLIENTS.get(self.warm_request_id)
                    if clients is not None:
                        clients.discard(self)
                        if not clients:
                            WARM_ACTIVE_CLIENTS.pop(self.warm_request_id, None)
            if self.prop_id:
                with WARM_LOCK:
                    clients = PROP_ACTIVE_CLIENTS.get(self.prop_id)
                    if clients is not None:
                        clients.discard(self)
                        if not clients:
                            PROP_ACTIVE_CLIENTS.pop(self.prop_id, None)

    def _read_stdout(self) -> None:
        assert self.proc.stdout is not None
        while True:
            headers = {}
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    return
                if line in (b"\r\n", b"\n"):
                    break
                key, value = line.decode("ascii").split(":", 1)
                headers[key.lower()] = value.strip()
            length = int(headers["content-length"])
            body = self.proc.stdout.read(length)
            self.messages.put(json.loads(body.decode("utf-8")))

    def _read_stderr(self) -> None:
        assert self.proc.stderr is not None
        while True:
            line = self.proc.stderr.readline()
            if not line:
                return
            self.stderr.put(line)

    def stderr_tail(self, limit: int = 4000) -> str:
        chunks = []
        while True:
            try:
                chunks.append(self.stderr.get_nowait())
            except queue.Empty:
                break
        return b"".join(chunks).decode("utf-8", errors="replace")[-limit:]

    def send(self, msg: dict) -> None:
        assert self.proc.stdin is not None
        body = json.dumps(msg, ensure_ascii=False).encode("utf-8")
        self.proc.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
        self.proc.stdin.flush()

    def request(self, method: str, params: dict | None = None) -> int:
        msg_id = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params or {}})
        return msg_id

    def notify(self, method: str, params: dict | None = None) -> None:
        self.send({"jsonrpc": "2.0", "method": method, "params": params or {}})

    def respond_to_server_request(self, msg: dict) -> bool:
        if "id" not in msg or "method" not in msg:
            return False
        method = msg.get("method")
        if method not in (
            "client/registerCapability",
            "client/unregisterCapability",
            "workspace/semanticTokens/refresh",
            "workspace/inlayHint/refresh",
            "workspace/diagnostic/refresh",
        ):
            return False
        self.send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
        return True

    def wait_for_id(self, msg_id: int, deadline: float, diagnostics: list[dict], cancel_check=None) -> dict:
        while time.time() < deadline:
            ensure_current_prop(self.prop_id, self.client_id)
            if cancel_check:
                cancel_check()
            try:
                msg = self.messages.get(timeout=0.2)
            except queue.Empty:
                continue
            if self.respond_to_server_request(msg):
                continue
            if msg.get("method") == "textDocument/publishDiagnostics":
                for diag in msg.get("params", {}).get("diagnostics", []):
                    if isinstance(diag, dict):
                        diagnostics.append(normalize_lsp_diagnostic(diag))
            if msg.get("id") == msg_id and "method" not in msg:
                return msg
        stderr = self.stderr_tail()
        if self.proc.poll() is not None:
            raise RuntimeError(f"Lean server exited before response id {msg_id}. {stderr}".strip())
        detail = f"timed out waiting for Lean response id {msg_id}"
        if stderr:
            detail += f". Lean/Lake stderr: {stderr}"
        raise TimeoutError(detail)


class LeanFileSession:
    def __init__(self, root: Path, file_path: Path, file_hash: str, warm_request_id: str | None = None, prop_id: str | None = None, cancel_check=None, client_id: str = "default"):
        self.root = root
        self.file_path = file_path
        self.file_hash = file_hash
        self.rel = display_file_path(root, file_path)
        self.uri = file_uri(file_path)
        self.root_uri = file_uri(root)
        self.client = LeanLspClient(root, warm_request_id, prop_id, client_id)
        self.lock = threading.Lock()
        self.diagnostics: list[dict] = []
        self.ready_at = ""
        self.cancel_check = cancel_check
        try:
            self._initialize()
        except Exception:
            self.close()
            raise

    def close(self) -> None:
        self.client.close()

    def _record_diagnostics(self, msg: dict) -> None:
        if msg.get("method") != "textDocument/publishDiagnostics":
            return
        self.diagnostics = []
        for diag in msg.get("params", {}).get("diagnostics", []):
            if isinstance(diag, dict):
                self.diagnostics.append(normalize_lsp_diagnostic(diag))

    def _initialize(self) -> None:
        deadline = time.time() + int(os.environ.get("LEAN_SURVEY_INIT_TIMEOUT", "120"))
        init_id = self.client.request("initialize", {
            "processId": os.getpid(),
            "rootUri": self.root_uri,
            "capabilities": {},
            "workspaceFolders": [{"uri": self.root_uri, "name": self.root.name}],
        })
        init = self.client.wait_for_id(init_id, deadline, self.diagnostics, self.cancel_check)
        if "error" in init:
            raise RuntimeError(init["error"].get("message", "Lean initialize failed"))
        self.client.notify("initialized", {})
        self.client.notify("textDocument/didOpen", {
            "dependencyBuildMode": "never",
            "textDocument": {
                "uri": self.uri,
                "languageId": "lean4",
                "version": 1,
                "text": self.file_path.read_text(encoding="utf-8"),
            }
        })

        completed = False
        while time.time() < deadline:
            ensure_current_prop(self.client.prop_id, self.client.client_id)
            if self.cancel_check:
                self.cancel_check()
            try:
                msg = self.client.messages.get(timeout=0.2)
            except queue.Empty:
                continue
            self._record_diagnostics(msg)
            if lean_file_progress_complete(msg, self.uri):
                completed = True
                break
            if lean_file_progress_fatal(msg, self.uri):
                detail = "; ".join(
                    d.get("message", "")
                    for d in self.diagnostics
                    if d.get("message")
                )
                raise RuntimeError(f"Lean reported a fatal file-processing error for {self.rel}. {detail}".strip())

        if not completed:
            raise TimeoutError(f"Lean did not finish processing {self.rel} before warm-up deadline")

        self.ready_at = now_iso()

    def query(self, line: int, column: int = 0, cancel_check=None) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            connect_id = self.client.request("$/lean/rpc/connect", {"uri": self.uri})
            connect = self.client.wait_for_id(connect_id, deadline, self.diagnostics, cancel_check)
            if "error" in connect:
                raise RuntimeError(connect["error"].get("message", "Lean RPC connect failed"))
            session_id = connect["result"]["sessionId"]
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            plain_position_params = {"textDocument": {"uri": self.uri}, "position": pos}
            errors = []

            def rpc_call(name: str, params, label: str, required: bool = False):
                try:
                    return self.call_rpc_locked(session_id, name, params, pos, deadline, cancel_check)
                except RuntimeError as exc:
                    if required:
                        raise
                    errors.append({"label": label, "method": name, "message": str(exc)})
                    return None

            goals = rpc_call(
                "Lean.Widget.getInteractiveGoals",
                plain_position_params,
                "Interactive goals",
                required=True,
            ) or {}
            term_goal = rpc_call(
                "Lean.Widget.getInteractiveTermGoal",
                plain_position_params,
                "Expected type",
            )
            interactive_diagnostics = rpc_call(
                "Lean.Widget.getInteractiveDiagnostics",
                {"lineRange?": {"start": max(0, line - 9), "end": line + 8}},
                "Interactive diagnostics",
            )
            if interactive_diagnostics is None:
                interactive_diagnostics = rpc_call(
                    "Lean.Widget.getInteractiveDiagnostics",
                    {"lineRange": {"start": max(0, line - 9), "end": line + 8}},
                    "Interactive diagnostics",
                )
            return {
                "sessionId": session_id,
                "goals": goals,
                "termGoal": term_goal,
                "interactiveDiagnostics": interactive_diagnostics,
                "allInteractiveDiagnostics": interactive_diagnostics,
                "rpcErrors": errors,
            }

    def call_rpc_locked(self, session_id, method: str, params, pos: dict, deadline: float, cancel_check=None):
        call_id = self.client.request("$/lean/rpc/call", {
            "sessionId": session_id,
            "method": method,
            "params": params,
            "textDocument": {"uri": self.uri},
            "position": pos,
        })
        response = self.client.wait_for_id(call_id, deadline, self.diagnostics, cancel_check)
        if "error" in response:
            raise RuntimeError(response["error"].get("message", f"{method} failed"))
        return response.get("result")

    def hover(self, line: int, column: int) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            hover_id = self.client.request("textDocument/hover", {
                "textDocument": {"uri": self.uri},
                "position": pos,
            })
            response = self.client.wait_for_id(hover_id, deadline, self.diagnostics)
            if "error" in response:
                raise RuntimeError(response["error"].get("message", "Lean hover failed"))
            return normalize_hover(response.get("result"))

    def definition(self, line: int, column: int) -> list[dict]:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            for method in ("textDocument/definition", "textDocument/declaration"):
                req_id = self.client.request(method, {
                    "textDocument": {"uri": self.uri},
                    "position": pos,
                })
                response = self.client.wait_for_id(req_id, deadline, self.diagnostics)
                if "error" in response:
                    continue
                locations = normalize_lsp_locations(response.get("result"))
                if locations:
                    return locations
            return []

    def info_hover(self, session_id, line: int, column: int, info_ref: dict) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            if not isinstance(info_ref, dict):
                raise RuntimeError("missing Lean info reference")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            result = self.call_rpc_locked(
                session_id,
                "Lean.Widget.InteractiveDiagnostics.infoToInteractive",
                info_ref,
                pos,
                deadline,
            )
            return normalize_info_popup(result)

    def trace_children(self, session_id, line: int, column: int, trace_ref: dict) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            result = self.call_rpc_locked(
                session_id,
                "Lean.Widget.lazyTraceChildrenToInteractive",
                trace_ref,
                pos,
                deadline,
            ) or []
            return {
                "children": [interactive_message_payload(item) for item in result if isinstance(item, (dict, list, str))],
                "raw": result,
            }

    def _read_stdout(self) -> None:
        assert self.proc.stdout is not None
        while True:
            headers = {}
            while True:
                line = self.proc.stdout.readline()
                if not line:
                    return
                if line in (b"\r\n", b"\n"):
                    break
                key, value = line.decode("ascii").split(":", 1)
                headers[key.lower()] = value.strip()
            length = int(headers["content-length"])
            body = self.proc.stdout.read(length)
            self.messages.put(json.loads(body.decode("utf-8")))

    def _read_stderr(self) -> None:
        assert self.proc.stderr is not None
        while True:
            line = self.proc.stderr.readline()
            if not line:
                return
            self.stderr.put(line)

    def stderr_tail(self, limit: int = 4000) -> str:
        chunks = []
        while True:
            try:
                chunks.append(self.stderr.get_nowait())
            except queue.Empty:
                break
        return b"".join(chunks).decode("utf-8", errors="replace")[-limit:]

    def send(self, msg: dict) -> None:
        assert self.proc.stdin is not None
        body = json.dumps(msg, ensure_ascii=False).encode("utf-8")
        self.proc.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode("ascii") + body)
        self.proc.stdin.flush()

    def request(self, method: str, params: dict | None = None) -> int:
        msg_id = self.next_id
        self.next_id += 1
        self.send({"jsonrpc": "2.0", "id": msg_id, "method": method, "params": params or {}})
        return msg_id

    def notify(self, method: str, params: dict | None = None) -> None:
        self.send({"jsonrpc": "2.0", "method": method, "params": params or {}})

    def respond_to_server_request(self, msg: dict) -> bool:
        if "id" not in msg or "method" not in msg:
            return False
        method = msg.get("method")
        if method not in (
            "client/registerCapability",
            "client/unregisterCapability",
            "workspace/semanticTokens/refresh",
            "workspace/inlayHint/refresh",
            "workspace/diagnostic/refresh",
        ):
            return False
        self.send({"jsonrpc": "2.0", "id": msg["id"], "result": None})
        return True

    def wait_for_id(self, msg_id: int, deadline: float, diagnostics: list[dict], cancel_check=None) -> dict:
        while time.time() < deadline:
            ensure_current_prop(self.prop_id, self.client_id)
            if cancel_check:
                cancel_check()
            try:
                msg = self.messages.get(timeout=0.2)
            except queue.Empty:
                continue
            if self.respond_to_server_request(msg):
                continue
            if msg.get("method") == "textDocument/publishDiagnostics":
                for diag in msg.get("params", {}).get("diagnostics", []):
                    if isinstance(diag, dict):
                        diagnostics.append(normalize_lsp_diagnostic(diag))
            if msg.get("id") == msg_id and "method" not in msg:
                return msg
        stderr = self.stderr_tail()
        if self.proc.poll() is not None:
            raise RuntimeError(f"Lean server exited before response id {msg_id}. {stderr}".strip())
        detail = f"timed out waiting for Lean response id {msg_id}"
        if stderr:
            detail += f". Lean/Lake stderr: {stderr}"
        raise TimeoutError(detail)


class LeanFileSession:
    def __init__(self, root: Path, file_path: Path, file_hash: str, warm_request_id: str | None = None, prop_id: str | None = None, cancel_check=None, client_id: str = "default"):
        self.root = root
        self.file_path = file_path
        self.file_hash = file_hash
        self.rel = display_file_path(root, file_path)
        self.uri = file_uri(file_path)
        self.root_uri = file_uri(root)
        self.client = LeanLspClient(root, warm_request_id, prop_id, client_id)
        self.lock = threading.Lock()
        self.diagnostics: list[dict] = []
        self.ready_at = ""
        self.cancel_check = cancel_check
        try:
            self._initialize()
        except Exception:
            self.close()
            raise

    def close(self) -> None:
        self.client.close()

    def _record_diagnostics(self, msg: dict) -> None:
        if msg.get("method") != "textDocument/publishDiagnostics":
            return
        self.diagnostics = []
        for diag in msg.get("params", {}).get("diagnostics", []):
            if isinstance(diag, dict):
                self.diagnostics.append(normalize_lsp_diagnostic(diag))

    def _initialize(self) -> None:
        deadline = time.time() + int(os.environ.get("LEAN_SURVEY_INIT_TIMEOUT", "120"))
        init_id = self.client.request("initialize", {
            "processId": os.getpid(),
            "rootUri": self.root_uri,
            "capabilities": {},
            "workspaceFolders": [{"uri": self.root_uri, "name": self.root.name}],
        })
        init = self.client.wait_for_id(init_id, deadline, self.diagnostics, self.cancel_check)
        if "error" in init:
            raise RuntimeError(init["error"].get("message", "Lean initialize failed"))
        self.client.notify("initialized", {})
        self.client.notify("textDocument/didOpen", {
            "dependencyBuildMode": "never",
            "textDocument": {
                "uri": self.uri,
                "languageId": "lean4",
                "version": 1,
                "text": self.file_path.read_text(encoding="utf-8"),
            }
        })

        completed = False
        while time.time() < deadline:
            ensure_current_prop(self.client.prop_id, self.client.client_id)
            if self.cancel_check:
                self.cancel_check()
            try:
                msg = self.client.messages.get(timeout=0.2)
            except queue.Empty:
                continue
            self._record_diagnostics(msg)
            if lean_file_progress_complete(msg, self.uri):
                completed = True
                break
            if lean_file_progress_fatal(msg, self.uri):
                detail = "; ".join(
                    d.get("message", "")
                    for d in self.diagnostics
                    if d.get("message")
                )
                raise RuntimeError(f"Lean reported a fatal file-processing error for {self.rel}. {detail}".strip())

        if not completed:
            raise TimeoutError(f"Lean did not finish processing {self.rel} before warm-up deadline")

        self.ready_at = now_iso()

    def query(self, line: int, column: int = 0, cancel_check=None) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            connect_id = self.client.request("$/lean/rpc/connect", {"uri": self.uri})
            connect = self.client.wait_for_id(connect_id, deadline, self.diagnostics, cancel_check)
            if "error" in connect:
                raise RuntimeError(connect["error"].get("message", "Lean RPC connect failed"))
            session_id = connect["result"]["sessionId"]
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            plain_position_params = {"textDocument": {"uri": self.uri}, "position": pos}
            errors = []

            def rpc_call(name: str, params, label: str, required: bool = False):
                try:
                    return self.call_rpc_locked(session_id, name, params, pos, deadline, cancel_check)
                except RuntimeError as exc:
                    if required:
                        raise
                    errors.append({"label": label, "method": name, "message": str(exc)})
                    return None

            goals = rpc_call(
                "Lean.Widget.getInteractiveGoals",
                plain_position_params,
                "Interactive goals",
                required=True,
            ) or {}
            term_goal = rpc_call(
                "Lean.Widget.getInteractiveTermGoal",
                plain_position_params,
                "Expected type",
            )
            interactive_diagnostics = rpc_call(
                "Lean.Widget.getInteractiveDiagnostics",
                {"lineRange?": {"start": max(0, line - 9), "end": line + 8}},
                "Interactive diagnostics",
            )
            if interactive_diagnostics is None:
                interactive_diagnostics = rpc_call(
                    "Lean.Widget.getInteractiveDiagnostics",
                    {"lineRange": {"start": max(0, line - 9), "end": line + 8}},
                    "Interactive diagnostics",
                )
            return {
                "sessionId": session_id,
                "goals": goals,
                "termGoal": term_goal,
                "interactiveDiagnostics": interactive_diagnostics,
                "allInteractiveDiagnostics": interactive_diagnostics,
                "rpcErrors": errors,
            }

    def call_rpc_locked(self, session_id, method: str, params, pos: dict, deadline: float, cancel_check=None):
        call_id = self.client.request("$/lean/rpc/call", {
            "sessionId": session_id,
            "method": method,
            "params": params,
            "textDocument": {"uri": self.uri},
            "position": pos,
        })
        response = self.client.wait_for_id(call_id, deadline, self.diagnostics, cancel_check)
        if "error" in response:
            raise RuntimeError(response["error"].get("message", f"{method} failed"))
        return response.get("result")

    def hover(self, line: int, column: int) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            hover_id = self.client.request("textDocument/hover", {
                "textDocument": {"uri": self.uri},
                "position": pos,
            })
            response = self.client.wait_for_id(hover_id, deadline, self.diagnostics)
            if "error" in response:
                raise RuntimeError(response["error"].get("message", "Lean hover failed"))
            return normalize_hover(response.get("result"))

    def definition(self, line: int, column: int) -> list[dict]:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            for method in ("textDocument/definition", "textDocument/declaration"):
                req_id = self.client.request(method, {
                    "textDocument": {"uri": self.uri},
                    "position": pos,
                })
                response = self.client.wait_for_id(req_id, deadline, self.diagnostics)
                if "error" in response:
                    continue
                locations = normalize_lsp_locations(response.get("result"))
                if locations:
                    return locations
            return []

    def info_hover(self, session_id, line: int, column: int, info_ref: dict) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            if not isinstance(info_ref, dict):
                raise RuntimeError("missing Lean info reference")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            result = self.call_rpc_locked(
                session_id,
                "Lean.Widget.InteractiveDiagnostics.infoToInteractive",
                info_ref,
                pos,
                deadline,
            )
            return normalize_info_popup(result)

    def trace_children(self, session_id, line: int, column: int, trace_ref: dict) -> dict:
        with self.lock:
            if self.client.proc.poll() is not None:
                raise RuntimeError("Lean server process exited")
            deadline = time.time() + int(os.environ.get("LEAN_SURVEY_CLICK_TIMEOUT", "6"))
            pos = {"line": max(0, line - 1), "character": max(0, column)}
            result = self.call_rpc_locked(
                session_id,
                "Lean.Widget.lazyTraceChildrenToInteractive",
                trace_ref,
                pos,
                deadline,
            ) or []
            return {
                "children": [interactive_message_payload(item) for item in result if isinstance(item, (dict, list, str))],
                "raw": result,
            }


def lean_client_id(value) -> str:
    clean = str(value or "").strip()
    return clean or "default"


def lean_claim_id(reviewer_code, client_id: str = "default") -> str:
    reviewer = str(reviewer_code or "").strip()
    if reviewer:
        return f"reviewer:{reviewer}"
    return f"client:{lean_client_id(client_id)}"


class StaleWarmRequest(RuntimeError):
    pass


def active_prop_id(client_id: str = "default") -> str:
    with WARM_LOCK:
        return CLIENT_ACTIVE_PROP.get(lean_client_id(client_id), "")


def ensure_current_prop(prop_id: str, client_id: str = "default") -> None:
    current = active_prop_id(client_id)
    if current and prop_id and prop_id != current:
        raise RuntimeError("stale Lean request canceled because a different proposition is active")


def touch_interactive_prop_cache(prop_id: str, client_id: str = "default") -> None:
    if prop_id:
        touch_prop_cache(prop_id, [lean_claim_id("", client_id)])


def next_state_request(prop_id: str, client_id: str = "default") -> int:
    global LEAN_STATE_LATEST_ID
    client_id = lean_client_id(client_id)
    with WARM_LOCK:
        LEAN_STATE_LATEST_ID += 1
        request_id = LEAN_STATE_LATEST_ID
        LEAN_STATE_LATEST_BY_CLIENT_PROP[(client_id, str(prop_id))] = request_id
        return request_id


def ensure_latest_state_request(prop_id: str, request_id: int, client_id: str = "default") -> None:
    client_id = lean_client_id(client_id)
    ensure_current_prop(prop_id, client_id)
    with WARM_LOCK:
        latest = LEAN_STATE_LATEST_BY_CLIENT_PROP.get((client_id, str(prop_id)))
    if latest is not None and latest != request_id:
        raise RuntimeError("stale Lean state request canceled because a newer line is selected")


def acquire_lean_session_init_slot(priority: str, prop_id: str = "", client_id: str = "default", cancel_check=None) -> None:
    global LEAN_SESSION_INIT_ACTIVE
    global LEAN_SESSION_INIT_WAITING_INTERACTIVE
    global LEAN_SESSION_INIT_WAITING_BACKGROUND
    priority = "background" if priority == "background" else "interactive"
    queued = True
    with LEAN_SESSION_INIT_COND:
        if priority == "interactive":
            LEAN_SESSION_INIT_WAITING_INTERACTIVE += 1
        else:
            LEAN_SESSION_INIT_WAITING_BACKGROUND += 1
        try:
            while True:
                ensure_current_prop(prop_id, client_id)
                if cancel_check:
                    cancel_check()
                interactive_block = priority == "background" and LEAN_SESSION_INIT_WAITING_INTERACTIVE > 0
                if LEAN_SESSION_INIT_ACTIVE < max(1, LEAN_SESSION_INIT_CONCURRENCY) and not interactive_block:
                    LEAN_SESSION_INIT_ACTIVE += 1
                    queued = False
                    if priority == "interactive":
                        LEAN_SESSION_INIT_WAITING_INTERACTIVE -= 1
                    else:
                        LEAN_SESSION_INIT_WAITING_BACKGROUND -= 1
                    return
                LEAN_SESSION_INIT_COND.wait(0.2)
        finally:
            if queued:
                if priority == "interactive":
                    LEAN_SESSION_INIT_WAITING_INTERACTIVE -= 1
                else:
                    LEAN_SESSION_INIT_WAITING_BACKGROUND -= 1
                LEAN_SESSION_INIT_COND.notify_all()


def release_lean_session_init_slot() -> None:
    global LEAN_SESSION_INIT_ACTIVE
    with LEAN_SESSION_INIT_COND:
        LEAN_SESSION_INIT_ACTIVE = max(0, LEAN_SESSION_INIT_ACTIVE - 1)
        LEAN_SESSION_INIT_COND.notify_all()


def lean_session_init_status() -> dict:
    with LEAN_SESSION_INIT_COND:
        return {
            "concurrency": max(1, LEAN_SESSION_INIT_CONCURRENCY),
            "active": LEAN_SESSION_INIT_ACTIVE,
            "waiting_interactive": LEAN_SESSION_INIT_WAITING_INTERACTIVE,
            "waiting_background": LEAN_SESSION_INIT_WAITING_BACKGROUND,
        }


def get_lean_session(root: Path, file_path: Path, file_hash: str, prop_id: str = "", warm_request_id: str | None = None, cancel_check=None, client_id: str = "default", priority: str = "interactive") -> LeanFileSession:
    ensure_current_prop(prop_id, client_id)
    if cancel_check:
        cancel_check()
    key = (str(root), display_file_path(root, file_path), file_hash)
    slot_acquired = False
    inflight = None
    while True:
        creator = False
        need_slot = False
        with LEAN_SESSIONS_LOCK:
            session = LEAN_SESSIONS.get(key)
            if session and session.client.proc.poll() is None:
                return session
            if session:
                session.close()
                LEAN_SESSIONS.pop(key, None)
            inflight = LEAN_SESSION_INFLIGHT.get(key)
            if inflight is None:
                need_slot = True

        if need_slot:
            acquire_lean_session_init_slot(priority, prop_id, client_id, cancel_check)
            slot_acquired = True
            with LEAN_SESSIONS_LOCK:
                session = LEAN_SESSIONS.get(key)
                if session and session.client.proc.poll() is None:
                    release_lean_session_init_slot()
                    slot_acquired = False
                    return session
                if session:
                    session.close()
                    LEAN_SESSIONS.pop(key, None)
                inflight = LEAN_SESSION_INFLIGHT.get(key)
                if inflight is None:
                    inflight = {"event": threading.Event(), "error": None}
                    LEAN_SESSION_INFLIGHT[key] = inflight
                    creator = True

        if creator:
            break

        if slot_acquired:
            release_lean_session_init_slot()
            slot_acquired = False

        event = inflight["event"]
        while not event.wait(0.2):
            ensure_current_prop(prop_id, client_id)
            if cancel_check:
                cancel_check()
        error = inflight.get("error")
        if error is not None:
            raise RuntimeError(f"Lean session initialization failed for {display_file_path(root, file_path)}: {error}")
        ensure_current_prop(prop_id, client_id)
        if cancel_check:
            cancel_check()

    session = None
    try:
        session = LeanFileSession(root, file_path, file_hash, warm_request_id, prop_id, cancel_check, client_id)
        ensure_current_prop(prop_id, client_id)
        if cancel_check:
            cancel_check()
        with LEAN_SESSIONS_LOCK:
            existing = LEAN_SESSIONS.get(key)
            if existing and existing.client.proc.poll() is None:
                session.close()
                session = existing
            else:
                LEAN_SESSIONS[key] = session
            if warm_request_id:
                with WARM_LOCK:
                    WARM_SESSION_KEYS.setdefault(str(warm_request_id), set()).add(key)
            if prop_id:
                with WARM_LOCK:
                    PROP_SESSION_KEYS.setdefault(str(prop_id), set()).add(key)
        return session
    except Exception as exc:
        if session is not None:
            session.close()
        inflight["error"] = exc
        raise
    finally:
        with LEAN_SESSIONS_LOCK:
            if LEAN_SESSION_INFLIGHT.get(key) is inflight:
                LEAN_SESSION_INFLIGHT.pop(key, None)
            inflight["event"].set()
        if slot_acquired:
            release_lean_session_init_slot()


def discard_lean_session(root: Path, file_path: Path, file_hash: str, prop_id: str = "") -> None:
    key = (str(root), display_file_path(root, file_path), file_hash)
    session = None
    with LEAN_SESSIONS_LOCK:
        session = LEAN_SESSIONS.pop(key, None)
    if prop_id:
        with WARM_LOCK:
            keys = PROP_SESSION_KEYS.get(str(prop_id))
            if keys is not None:
                keys.discard(key)
    if session is not None:
        session.close()


def run_lean_rpc_state(root: Path, file_path: Path, line: int, column: int, context: list[dict], prop_id: str = "", state_request_id: int | None = None, client_id: str = "default") -> dict:
    rel = display_file_path(root, file_path)
    file_hash = hashlib.sha256(file_path.read_bytes()).hexdigest()
    cancel_check = (lambda: ensure_latest_state_request(prop_id, state_request_id, client_id)) if state_request_id is not None else None
    if cancel_check:
        cancel_check()
    session = get_lean_session(root, file_path, file_hash, prop_id, cancel_check=cancel_check, client_id=client_id)
    touch_interactive_prop_cache(prop_id, client_id)
    try:
        query = session.query(line, column, cancel_check)
    except TimeoutError:
        discard_lean_session(root, file_path, file_hash, prop_id)
        raise
    goals = query.get("goals") or {}
    structured_goals = normalize_goals(goals)
    term_goal = normalize_term_goal(query.get("termGoal"))
    raw_interactive_diagnostics = query.get("interactiveDiagnostics") or []
    interactive_diagnostics = [
        normalize_interactive_diagnostic(diag)
        for diag in raw_interactive_diagnostics
        if isinstance(diag, dict)
    ]
    raw_all_interactive_diagnostics = query.get("allInteractiveDiagnostics") or []
    all_interactive_diagnostics = [
        normalize_interactive_diagnostic(diag)
        for diag in raw_all_interactive_diagnostics
        if isinstance(diag, dict)
    ]
    nearby_messages = [d for d in session.diagnostics if abs(int(d.get("line", line)) - line) <= 8]
    return {
        "available": True,
        "mode": "rpc",
        "file": rel,
        "line": line,
        "column": column,
        "rpcSessionId": query.get("sessionId"),
        "context": context,
        "messages": nearby_messages,
        "allMessages": session.diagnostics,
        "interactiveMessages": interactive_diagnostics,
        "allInteractiveMessages": all_interactive_diagnostics,
        "goal": format_goals(goals),
        "goals": structured_goals,
        "goalCount": len(structured_goals),
        "termGoal": term_goal,
        "rpcErrors": query.get("rpcErrors") or [],
        "status": "complete" if not structured_goals else "goals",
        "note": f"Live Lean RPC state. Session warmed at {session.ready_at}.",
    }


def load_data() -> dict:
    if not DATA_PATH.exists():
        raise RuntimeError(f"Missing {DATA_PATH}; run extract_survey_data.py first")
    return json.loads(DATA_PATH.read_text(encoding="utf-8"))


def js_stable_hash(text: str) -> int:
    value = 0
    for ch in str(text or ""):
        value = ((value << 5) - value + ord(ch)) & 0xFFFFFFFF
        if value >= 0x80000000:
            value -= 0x100000000
    return abs(value)


def method_slots_swapped(prop_id: str) -> bool:
    return js_stable_hash(prop_id) % 2 == 1


def canonical_preference_choice(prop_id: str, ui_choice: int) -> int:
    if ui_choice == 0:
        return ui_choice
    return -ui_choice if method_slots_swapped(prop_id) else ui_choice


def db_connect() -> sqlite3.Connection:
    db = sqlite3.connect(DB_PATH, timeout=max(1.0, SQLITE_BUSY_TIMEOUT_MS / 1000))
    db.execute(f"PRAGMA busy_timeout = {max(1, SQLITE_BUSY_TIMEOUT_MS)}")
    return db


def init_db() -> None:
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    with db_connect() as db:
        db.execute("PRAGMA journal_mode = WAL")
        response_cols = [row[1] for row in db.execute("PRAGMA table_info(responses)").fetchall()]
        if response_cols and "method_id" not in response_cols:
            legacy_name = f"responses_legacy_{int(time.time())}"
            db.execute(f"ALTER TABLE responses RENAME TO {legacy_name}")
        db.execute("""
            CREATE TABLE IF NOT EXISTS responses (
                reviewer_code TEXT NOT NULL,
                proposition_id TEXT NOT NULL,
                method_id TEXT NOT NULL,
                metric_id TEXT NOT NULL,
                score INTEGER NOT NULL,
                note TEXT NOT NULL DEFAULT '',
                updated_at TEXT NOT NULL,
                PRIMARY KEY (reviewer_code, proposition_id, method_id, metric_id)
            )
        """)
        db.execute("""
            CREATE TABLE IF NOT EXISTS overall_notes (
                reviewer_code TEXT NOT NULL,
                proposition_id TEXT NOT NULL,
                note TEXT NOT NULL DEFAULT '',
                updated_at TEXT NOT NULL,
                PRIMARY KEY (reviewer_code, proposition_id)
            )
        """)
        db.execute("""
            CREATE TABLE IF NOT EXISTS preference_responses (
                reviewer_code TEXT NOT NULL,
                proposition_id TEXT NOT NULL,
                question_id TEXT NOT NULL,
                choice INTEGER NOT NULL,
                updated_at TEXT NOT NULL,
                PRIMARY KEY (reviewer_code, proposition_id, question_id)
            )
        """)
        db.execute("""
            CREATE TABLE IF NOT EXISTS schema_meta (
                key TEXT PRIMARY KEY,
                value TEXT NOT NULL
            )
        """)
        marker = db.execute(
            "SELECT value FROM schema_meta WHERE key = 'preference_choice_basis'"
        ).fetchone()
        if not marker:
            try:
                data = load_data()
                swapped_ids = [
                    prop.get("id", "")
                    for prop in data.get("propositions", [])
                    if prop.get("id", "") and method_slots_swapped(prop.get("id", ""))
                ]
                if swapped_ids:
                    placeholders = ",".join("?" for _ in swapped_ids)
                    db.execute(
                        f"UPDATE preference_responses SET choice = -choice WHERE choice != 0 AND proposition_id IN ({placeholders})",
                        swapped_ids,
                    )
            except Exception as exc:
                print(f"warning: could not migrate preference choices to method basis: {exc}", flush=True)
            db.execute(
                "INSERT INTO schema_meta (key, value) VALUES ('preference_choice_basis', 'canonical_method_v1')"
            )
        db.execute("""
            CREATE TABLE IF NOT EXISTS reviewers (
                reviewer_code TEXT PRIMARY KEY,
                created_at TEXT NOT NULL,
                disabled_at TEXT NOT NULL DEFAULT ''
            )
        """)
        reviewer_cols = [row[1] for row in db.execute("PRAGMA table_info(reviewers)").fetchall()]
        if "disabled_at" not in reviewer_cols:
            db.execute("ALTER TABLE reviewers ADD COLUMN disabled_at TEXT NOT NULL DEFAULT ''")
        db.execute("""
            CREATE TABLE IF NOT EXISTS reviewer_tutorials (
                reviewer_code TEXT NOT NULL,
                tutorial_version TEXT NOT NULL,
                completed_at TEXT NOT NULL,
                updated_at TEXT NOT NULL,
                PRIMARY KEY (reviewer_code, tutorial_version)
            )
        """)
        db.execute("""
            CREATE TABLE IF NOT EXISTS removed_reviewers (
                reviewer_code TEXT PRIMARY KEY,
                removed_at TEXT NOT NULL
            )
        """)
        db.execute("""
            CREATE TABLE IF NOT EXISTS reviewer_invites (
                reviewer_code TEXT PRIMARY KEY,
                email TEXT NOT NULL,
                access_url TEXT NOT NULL,
                sent_at TEXT NOT NULL
            )
        """)
        invite_cols = [row[1] for row in db.execute("PRAGMA table_info(reviewer_invites)").fetchall()]
        if "invite_token" not in invite_cols:
            db.execute("ALTER TABLE reviewer_invites ADD COLUMN invite_token TEXT NOT NULL DEFAULT ''")
        if "email_normalized" not in invite_cols:
            db.execute("ALTER TABLE reviewer_invites ADD COLUMN email_normalized TEXT NOT NULL DEFAULT ''")
        if "created_at" not in invite_cols:
            db.execute("ALTER TABLE reviewer_invites ADD COLUMN created_at TEXT NOT NULL DEFAULT ''")
        invite_rows = db.execute(
            "SELECT reviewer_code, email, invite_token, email_normalized, created_at, sent_at FROM reviewer_invites"
        ).fetchall()
        removed_codes = {
            row[0]
            for row in db.execute("SELECT reviewer_code FROM removed_reviewers")
            if row[0]
        }
        used_emails = set()
        for reviewer_code, email, invite_token, email_normalized, created_at, sent_at in invite_rows:
            normalized = normalize_email(email)
            if normalized in used_emails:
                normalized = ""
            elif normalized:
                used_emails.add(normalized)
            if not invite_token:
                invite_token = generate_invite_token(db)
            db.execute(
                """
                UPDATE reviewer_invites
                SET invite_token = ?, email_normalized = ?, created_at = ?
                WHERE reviewer_code = ?
                """,
                (invite_token, normalized, created_at or sent_at or now_iso(), reviewer_code),
            )
            if reviewer_code and reviewer_code not in removed_codes:
                db.execute(
                    """
                    INSERT INTO reviewers (reviewer_code, created_at, disabled_at)
                    VALUES (?, ?, '')
                    ON CONFLICT(reviewer_code) DO NOTHING
                    """,
                    (reviewer_code, created_at or sent_at or now_iso()),
                )
        db.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_reviewer_invites_token ON reviewer_invites(invite_token) WHERE invite_token != ''")
        db.execute("CREATE UNIQUE INDEX IF NOT EXISTS idx_reviewer_invites_email_normalized ON reviewer_invites(email_normalized) WHERE email_normalized != ''")
        reviewer_codes = set()
        configured = os.environ.get("SURVEY_REVIEWER_CODES", "")
        reviewer_codes.update(code.strip() for code in configured.split(",") if code.strip())
        if REVIEWERS_PATH.exists():
            for line in REVIEWERS_PATH.read_text(encoding="utf-8").splitlines():
                code = line.split("#", 1)[0].strip()
                if code:
                    reviewer_codes.add(code)
        ts = now_iso()
        for code in reviewer_codes:
            db.execute(
                """
                INSERT INTO reviewers (reviewer_code, created_at)
                VALUES (?, ?)
                ON CONFLICT(reviewer_code) DO NOTHING
                """,
                (code, ts),
            )
        db.commit()


def now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def iso_z_epoch(value: str) -> float:
    if not value:
        return 0
    try:
        return datetime.strptime(value, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc).timestamp()
    except ValueError:
        return 0


def valid_email(value: str) -> bool:
    return bool(re.match(r"^[^@\s]+@[^@\s]+\.[^@\s]+$", str(value or "").strip()))


def normalize_email(value: str) -> str:
    return str(value or "").strip().lower()


def reviewer_code_taken(db: sqlite3.Connection, code: str) -> bool:
    for table in ("reviewers", "removed_reviewers", "responses", "overall_notes", "preference_responses"):
        row = db.execute(f"SELECT 1 FROM {table} WHERE reviewer_code = ? LIMIT 1", (code,)).fetchone()
        if row:
            return True
    return False


def generate_reviewer_code(db: sqlite3.Connection) -> str:
    for _ in range(100):
        code = "R-" + "".join(secrets.choice(REVIEWER_CODE_ALPHABET) for _ in range(8))
        if not reviewer_code_taken(db, code):
            return code
    raise RuntimeError("could not generate a unique reviewer code")


def generate_invite_token(db: sqlite3.Connection) -> str:
    for _ in range(100):
        token = secrets.token_urlsafe(32)
        row = db.execute(
            "SELECT 1 FROM reviewer_invites WHERE invite_token = ? LIMIT 1",
            (token,),
        ).fetchone()
        if not row:
            return token
    raise RuntimeError("could not generate a unique invite token")


def reviewer_link(access_url: str, token: str) -> str:
    return f"{access_url.rstrip('/')}/#invite={quote(token, safe='')}"


def reviewer_invite_body(access_url: str, token: str) -> str:
    link = reviewer_link(access_url, token)
    return f"""Dear reviewer,

You have been invited to review a set of Lean formalizations for a research study on faithfulness of mathematical formalization.

Purpose of the survey
The survey asks experts to evaluate two Lean formalizations of selected Euclid propositions. For each formalization, you will score Step Fidelity: how faithfully the Lean proof represents the textbook's mathematical steps and dependencies. After scoring both formalizations for a proposition, you will answer comparison questions about mathematical transparency, textbook representation, and your overall preference.

The goal is to evaluate how well the formalizations preserve the textbook proof and how useful each formalization is for following the mathematical argument.

How to access the survey
1. Open this link:
   {link}
2. If this is your first time, please go through the short interactive tutorial. It explains the review workflow, assigned propositions, Lean inspection tools, sentence-mapping aids, and autosave behavior.

Thank you for contributing your expertise.
"""


def send_invite_email(to_email: str, subject: str, body: str) -> None:
    from_email = os.environ.get("SURVEY_EMAIL_FROM", "faithfulness-survey@localhost")
    msg = EmailMessage()
    msg["From"] = from_email
    msg["To"] = to_email
    msg["Subject"] = subject
    msg.set_content(body)

    smtp_host = os.environ.get("SURVEY_SMTP_HOST", "").strip()
    if smtp_host:
        port = int(os.environ.get("SURVEY_SMTP_PORT", "465" if os.environ.get("SURVEY_SMTP_SSL") else "25"))
        use_ssl = os.environ.get("SURVEY_SMTP_SSL", "").lower() in ("1", "true", "yes")
        use_tls = os.environ.get("SURVEY_SMTP_TLS", "").lower() in ("1", "true", "yes")
        client_cls = smtplib.SMTP_SSL if use_ssl else smtplib.SMTP
        with client_cls(smtp_host, port, timeout=20) as smtp:
            if use_tls and not use_ssl:
                smtp.starttls()
            username = os.environ.get("SURVEY_SMTP_USERNAME", "")
            password = os.environ.get("SURVEY_SMTP_PASSWORD", "")
            if username:
                smtp.login(username, password)
            smtp.send_message(msg)
        return

    sendmail = os.environ.get("SURVEY_SENDMAIL", "")
    candidates = [Path(sendmail)] if sendmail else [Path("/usr/sbin/sendmail"), Path("/usr/lib/sendmail")]
    sendmail_path = next((path for path in candidates if path.exists() and os.access(path, os.X_OK)), None)
    if sendmail_path:
        proc = subprocess.run(
            [str(sendmail_path), "-t", "-oi"],
            input=msg.as_string(),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=20,
        )
        if proc.returncode != 0:
            raise RuntimeError(proc.stderr.strip() or f"sendmail exited with code {proc.returncode}")
        return

    raise RuntimeError("email sending is not configured; set SURVEY_SMTP_HOST or SURVEY_SENDMAIL")


def public_access_url(handler: BaseHTTPRequestHandler, explicit: str = "") -> str:
    access_url = str(explicit or os.environ.get("SURVEY_PUBLIC_URL", "")).strip().rstrip("/")
    if access_url:
        return access_url
    host = handler.headers.get("Host", "127.0.0.1:8765")
    scheme = handler.headers.get("X-Forwarded-Proto", "").split(",", 1)[0].strip().lower()
    if scheme not in ("http", "https"):
        try:
            scheme = str(json.loads(handler.headers.get("Cf-Visitor", "{}")).get("scheme", "")).lower()
        except json.JSONDecodeError:
            scheme = ""
    if scheme not in ("http", "https"):
        scheme = "http"
    return f"{scheme}://{host}"


def reviewer_code_for_token(token: str) -> str:
    clean = str(token or "").strip()
    if not clean:
        return ""
    with db_connect() as db:
        row = db.execute(
            "SELECT reviewer_code FROM reviewer_invites WHERE invite_token = ?",
            (clean,),
        ).fetchone()
    if not row:
        return ""
    code = row[0]
    return code if reviewer_exists(code) else ""


def reviewer_from_payload(payload: dict) -> str:
    reviewer = str(payload.get("reviewer_code", "")).strip()
    if reviewer:
        return reviewer
    return reviewer_code_for_token(str(payload.get("reviewer_token", "")).strip())


def rate_limit_reviewer_link(ip: str) -> bool:
    now = time.time()
    with INVITE_RATE_LOCK:
        recent = [
            item for item in INVITE_RATE_BY_IP.get(ip, [])
            if now - item <= max(1, INVITE_RATE_WINDOW_SECONDS)
        ]
        if len(recent) >= max(1, INVITE_RATE_MAX_PER_IP):
            INVITE_RATE_BY_IP[ip] = recent
            return False
        recent.append(now)
        INVITE_RATE_BY_IP[ip] = recent
    return True


def admin_secret_configured() -> bool:
    return bool(
        os.environ.get("SURVEY_ADMIN_PASSWORD_HASH")
        or os.environ.get("SURVEY_ADMIN_PASSWORD")
        or os.environ.get("SURVEY_ADMIN_TOKEN")
        or ADMIN_PASSWORD_HASH_PATH.exists()
    )


def configured_admin_hash() -> str:
    configured = os.environ.get("SURVEY_ADMIN_PASSWORD_HASH", "").strip()
    if configured:
        return configured
    if ADMIN_PASSWORD_HASH_PATH.exists():
        return ADMIN_PASSWORD_HASH_PATH.read_text(encoding="utf-8").strip()
    return ""


def verify_admin_secret(value: str) -> bool:
    value = str(value or "")
    expected_hash = configured_admin_hash()
    if expected_hash:
        digest = hashlib.sha256(value.encode("utf-8")).hexdigest()
        if expected_hash.startswith("sha256:"):
            expected_hash = expected_hash.split(":", 1)[1]
        return hmac.compare_digest(digest, expected_hash)
    expected = os.environ.get("SURVEY_ADMIN_PASSWORD") or os.environ.get("SURVEY_ADMIN_TOKEN") or ""
    return bool(expected) and hmac.compare_digest(value, expected)


def parse_cookies(header: str) -> dict[str, str]:
    cookies: dict[str, str] = {}
    for item in str(header or "").split(";"):
        if "=" not in item:
            continue
        key, value = item.split("=", 1)
        cookies[key.strip()] = unquote(value.strip())
    return cookies


def create_admin_session() -> str:
    token = secrets.token_urlsafe(32)
    expires = time.time() + max(300, ADMIN_SESSION_SECONDS)
    with ADMIN_SESSIONS_LOCK:
        ADMIN_SESSIONS[token] = expires
    return token


def admin_session_valid(token: str) -> bool:
    if not token:
        return False
    now = time.time()
    with ADMIN_SESSIONS_LOCK:
        expires = ADMIN_SESSIONS.get(token)
        if not expires:
            return False
        if expires < now:
            ADMIN_SESSIONS.pop(token, None)
            return False
        ADMIN_SESSIONS[token] = now + max(300, ADMIN_SESSION_SECONDS)
        return True


def destroy_admin_session(token: str) -> None:
    if not token:
        return
    with ADMIN_SESSIONS_LOCK:
        ADMIN_SESSIONS.pop(token, None)


def audit_admin(action: str, detail: str = "") -> None:
    suffix = f" {detail}" if detail else ""
    print(f"[admin] {now_iso()} {action}{suffix}", flush=True)


def reviewer_exists(reviewer: str) -> bool:
    reviewer = reviewer.strip()
    if not reviewer:
        return False
    with db_connect() as db:
        removed = db.execute(
            "SELECT 1 FROM removed_reviewers WHERE reviewer_code = ?",
            (reviewer,),
        ).fetchone()
        if removed:
            return False
        registered = db.execute(
            "SELECT disabled_at FROM reviewers WHERE reviewer_code = ?",
            (reviewer,),
        ).fetchone()
        if registered:
            return not bool(registered[0])
        existing_response = db.execute(
            "SELECT 1 FROM responses WHERE reviewer_code = ? LIMIT 1",
            (reviewer,),
        ).fetchone()
        if existing_response:
            return True
        existing_note = db.execute(
            "SELECT 1 FROM overall_notes WHERE reviewer_code = ? LIMIT 1",
            (reviewer,),
        ).fetchone()
        if existing_note:
            return True
        existing_preference = db.execute(
            "SELECT 1 FROM preference_responses WHERE reviewer_code = ? LIMIT 1",
            (reviewer,),
        ).fetchone()
        return bool(existing_preference)


def ready_prop_ids(data: dict) -> list[str]:
    ids = []
    for prop in data.get("propositions", []):
        methods = prop.get("methods", {})
        if methods.get("leaneuclid", {}).get("available") and methods.get("new_method", {}).get("available"):
            ids.append(prop.get("id", ""))
    return [item for item in ids if item]


def review_assignment_pool_ids(data: dict) -> list[str]:
    ready_ids = set(ready_prop_ids(data))
    prop_ids = {prop.get("id", "") for prop in data.get("propositions", [])}
    return [
        prop_id
        for prop_id in REVIEW_ASSIGNMENT_POOL_PROP_IDS
        if prop_id in prop_ids and prop_id in ready_ids
    ]


def required_response_count(data: dict) -> int:
    return min(REVIEW_ASSIGNMENT_COUNT, len(review_assignment_pool_ids(data))) * len(data.get("rubric", {}).get("metrics", [])) * 2


def required_preference_count(data: dict) -> int:
    return min(REVIEW_ASSIGNMENT_COUNT, len(review_assignment_pool_ids(data))) * len(data.get("preference_questions", {}).get("questions", []))


def reviewer_assignment(data: dict, reviewer_code: str) -> list[str]:
    pool_ids = review_assignment_pool_ids(data)
    if not reviewer_code:
        return []
    reviewer_code = reviewer_code.strip()
    count = min(max(0, REVIEW_ASSIGNMENT_COUNT), len(pool_ids))
    ranked = sorted(
        pool_ids,
        key=lambda prop_id: hashlib.sha256(f"{reviewer_code}::{prop_id}".encode("utf-8")).hexdigest(),
    )
    assigned = ranked[:count]
    for prop_id in REVIEW_ASSIGNMENT_EXTRA_PROP_IDS.get(reviewer_code, ()):
        if prop_id in pool_ids and prop_id not in assigned:
            assigned.append(prop_id)
    return assigned


def prop_reviewable(data: dict, reviewer_code: str, prop_id: str) -> bool:
    return prop_id in set(reviewer_assignment(data, reviewer_code))


def reviewer_progress_payload(reviewer: str, include_code: bool = False) -> dict:
    data = load_data()
    with db_connect() as db:
        rows = db.execute(
            "SELECT proposition_id, method_id, metric_id, score, note, updated_at FROM responses WHERE reviewer_code = ?",
            (reviewer,),
        ).fetchall()
        notes = db.execute(
            "SELECT proposition_id, note, updated_at FROM overall_notes WHERE reviewer_code = ?",
            (reviewer,),
        ).fetchall()
        preferences = db.execute(
            "SELECT proposition_id, question_id, choice, updated_at FROM preference_responses WHERE reviewer_code = ?",
            (reviewer,),
        ).fetchall()
    assigned_ids = reviewer_assignment(data, reviewer)
    payload = {
        "assigned_proposition_ids": assigned_ids,
        "review_target_count": len(assigned_ids),
        "responses": [
            {"proposition_id": r[0], "method_id": r[1], "metric_id": r[2], "score": r[3], "note": r[4], "updated_at": r[5]}
            for r in rows
        ],
        "overall_notes": [
            {"proposition_id": r[0], "note": r[1], "updated_at": r[2]} for r in notes
        ],
        "preferences": [
            {"proposition_id": r[0], "question_id": r[1], "choice": r[2], "updated_at": r[3]} for r in preferences
        ],
    }
    if include_code:
        payload["reviewer_code"] = reviewer
    return payload


def reviewer_tutorial_payload(reviewer: str, include_code: bool = False) -> dict:
    with db_connect() as db:
        row = db.execute(
            """
            SELECT completed_at, updated_at FROM reviewer_tutorials
            WHERE reviewer_code = ? AND tutorial_version = ?
            """,
            (reviewer, TUTORIAL_VERSION),
        ).fetchone()
    payload = {
        "tutorial_version": TUTORIAL_VERSION,
        "completed": bool(row),
        "completed_at": row[0] if row else "",
        "updated_at": row[1] if row else "",
    }
    if include_code:
        payload["reviewer_code"] = reviewer
    return payload


def admin_summary_payload() -> dict:
    data = load_data()
    metrics = data.get("rubric", {}).get("metrics", [])
    preference_questions = data.get("preference_questions", {}).get("questions", [])
    ready_ids = set(ready_prop_ids(data))
    required_per_reviewer = required_response_count(data)
    required_preferences_per_reviewer = required_preference_count(data)
    with db_connect() as db:
        db.row_factory = sqlite3.Row
        reviewers = [dict(row) for row in db.execute(
            "SELECT reviewer_code, created_at, disabled_at FROM reviewers ORDER BY reviewer_code"
        )]
        removed_codes = {
            row["reviewer_code"]
            for row in db.execute("SELECT reviewer_code FROM removed_reviewers")
        }
        responses = [dict(row) for row in db.execute(
            "SELECT reviewer_code, proposition_id, method_id, metric_id, score, note, updated_at FROM responses"
        )]
        notes = [dict(row) for row in db.execute(
            "SELECT reviewer_code, proposition_id, note, updated_at FROM overall_notes"
        )]
        preferences = [dict(row) for row in db.execute(
            "SELECT reviewer_code, proposition_id, question_id, choice, updated_at FROM preference_responses"
        )]
        tutorials = {
            row["reviewer_code"]: dict(row)
            for row in db.execute("SELECT reviewer_code, completed_at, updated_at FROM reviewer_tutorials")
        }

    responses_by_reviewer: dict[str, list[dict]] = {}
    notes_by_reviewer: dict[str, list[dict]] = {}
    preferences_by_reviewer: dict[str, list[dict]] = {}
    for row in responses:
        responses_by_reviewer.setdefault(row["reviewer_code"], []).append(row)
    for row in notes:
        notes_by_reviewer.setdefault(row["reviewer_code"], []).append(row)
    for row in preferences:
        preferences_by_reviewer.setdefault(row["reviewer_code"], []).append(row)

    reviewer_rows = []
    reviewer_codes = sorted(({r["reviewer_code"] for r in reviewers} | set(responses_by_reviewer) | set(notes_by_reviewer) | set(preferences_by_reviewer)) - removed_codes)
    reviewer_lookup = {r["reviewer_code"]: r for r in reviewers}
    for code in reviewer_codes:
        row = reviewer_lookup.get(code, {"reviewer_code": code, "created_at": "", "disabled_at": ""})
        assigned_list = reviewer_assignment(data, code)
        assigned_ids = set(assigned_list)
        required_for_reviewer = len(assigned_list) * len(metrics) * 2
        required_preferences_for_reviewer = len(assigned_list) * len(preference_questions)
        ready_responses = [r for r in responses_by_reviewer.get(code, []) if r["proposition_id"] in assigned_ids]
        ready_preferences = [r for r in preferences_by_reviewer.get(code, []) if r["proposition_id"] in assigned_ids]
        any_input = bool(
            responses_by_reviewer.get(code)
            or preferences_by_reviewer.get(code)
            or any(str(n.get("note", "")).strip() for n in notes_by_reviewer.get(code, []))
        )
        response_count = len({(r["proposition_id"], r["method_id"], r["metric_id"]) for r in ready_responses})
        preference_count = len({(r["proposition_id"], r["question_id"]) for r in ready_preferences})
        done = (
            required_for_reviewer > 0
            and response_count >= required_for_reviewer
            and preference_count >= required_preferences_for_reviewer
        )
        last_activity = max(
            [r.get("updated_at", "") for r in responses_by_reviewer.get(code, [])]
            + [n.get("updated_at", "") for n in notes_by_reviewer.get(code, [])]
            + [p.get("updated_at", "") for p in preferences_by_reviewer.get(code, [])]
            + [tutorials.get(code, {}).get("updated_at", "")],
            default="",
        )
        reviewer_rows.append({
            "reviewer_code": code,
            "created_at": row.get("created_at", ""),
            "disabled_at": row.get("disabled_at", ""),
            "active": not bool(row.get("disabled_at", "")),
            "status": "done" if done else ("in_progress" if any_input else "not_started"),
            "response_count": response_count,
            "preference_response_count": preference_count,
            "required_response_count": required_for_reviewer,
            "required_preference_response_count": required_preferences_for_reviewer,
            "assigned_proposition_ids": assigned_list,
            "tutorial_completed": bool(tutorials.get(code, {}).get("completed_at")),
            "last_activity": last_activity,
        })

    responses_by_prop_reviewer: dict[tuple[str, str], set[tuple[str, str]]] = {}
    for row in responses:
        responses_by_prop_reviewer.setdefault((row["proposition_id"], row["reviewer_code"]), set()).add((row["method_id"], row["metric_id"]))
    preferences_by_prop_reviewer: dict[tuple[str, str], set[str]] = {}
    for row in preferences:
        preferences_by_prop_reviewer.setdefault((row["proposition_id"], row["reviewer_code"]), set()).add(row["question_id"])

    prop_rows = []
    expected_prop_entries = len(metrics) * 2
    expected_prop_preferences = len(preference_questions)
    assignment_pool_ids = set(REVIEW_ASSIGNMENT_POOL_PROP_IDS)
    for prop in data.get("propositions", []):
        prop_id = prop.get("id", "")
        available = {k: bool(v.get("available")) for k, v in prop.get("methods", {}).items()}
        started = 0
        done = 0
        for reviewer in reviewer_rows:
            if not reviewer["active"]:
                continue
            if prop_id not in set(reviewer.get("assigned_proposition_ids", [])):
                continue
            entries = responses_by_prop_reviewer.get((prop_id, reviewer["reviewer_code"]), set())
            preference_entries = preferences_by_prop_reviewer.get((prop_id, reviewer["reviewer_code"]), set())
            if entries or preference_entries:
                started += 1
            if prop_id in ready_ids and len(entries) >= expected_prop_entries and len(preference_entries) >= expected_prop_preferences:
                done += 1
        prop_rows.append({
            "id": prop_id,
            "display": prop.get("display", prop_id),
            "number": prop.get("number"),
            "title": prop.get("title", ""),
            "ready": prop_id in ready_ids,
            "in_assignment_pool": prop_id in assignment_pool_ids,
            "methodAvailability": available,
            "started_reviewers": started,
            "done_reviewers": done,
            "missing_mappings": [
                method_id for method_id, method in prop.get("methods", {}).items()
                if method.get("available") and not method.get("line_text_mappings")
            ],
            "diagram_available": bool(prop.get("diagram", {}).get("available")),
        })

    health = {
        "missing_new_method": [p["id"] for p in prop_rows if not p["methodAvailability"].get("new_method")],
        "missing_leaneuclid": [p["id"] for p in prop_rows if not p["methodAvailability"].get("leaneuclid")],
        "missing_diagrams": [p["id"] for p in prop_rows if not p["diagram_available"]],
        "missing_mappings": [{"proposition_id": p["id"], "methods": p["missing_mappings"]} for p in prop_rows if p["missing_mappings"]],
    }

    active_reviewers = [r for r in reviewer_rows if r["active"]]
    recent_cutoff = time.time() - 15 * 60
    recently_active = []
    for reviewer in active_reviewers:
        last = reviewer.get("last_activity", "")
        if not last:
            continue
        last_epoch = iso_z_epoch(last)
        if not last_epoch:
            continue
        if last_epoch >= recent_cutoff:
            recently_active.append(reviewer)

    return {
        "version": data.get("version", ""),
        "methods": data.get("methods", {}),
        "rubric_metric_count": len(metrics),
        "proposition_count": len(data.get("propositions", [])),
        "ready_proposition_count": len(ready_ids),
        "missing_pair_count": len(data.get("propositions", [])) - len(ready_ids),
        "reviewer_count": len(reviewer_rows),
        "active_reviewer_count": len(active_reviewers),
        "recent_active_reviewer_count": len(recently_active),
        "started_reviewer_count": len([r for r in reviewer_rows if r["status"] != "not_started"]),
        "done_reviewer_count": len([r for r in reviewer_rows if r["status"] == "done"]),
        "response_count": len(responses),
        "preference_response_count": len(preferences),
        "overall_note_count": len(notes),
        "required_response_count_per_reviewer": required_per_reviewer,
        "required_preference_response_count_per_reviewer": required_preferences_per_reviewer,
        "reviewers": reviewer_rows,
        "propositions": prop_rows,
        "health": health,
    }


def admin_scores_payload() -> dict:
    data = load_data()
    with db_connect() as db:
        db.row_factory = sqlite3.Row
        removed_codes = {
            row["reviewer_code"]
            for row in db.execute("SELECT reviewer_code FROM removed_reviewers")
        }
        rows = [dict(row) for row in db.execute(
            """
            SELECT reviewer_code, proposition_id, method_id, metric_id, score, updated_at
            FROM responses
            ORDER BY reviewer_code, proposition_id, method_id, metric_id
            """
        ) if row["reviewer_code"] not in removed_codes]
        preference_rows = [dict(row) for row in db.execute(
            """
            SELECT reviewer_code, proposition_id, question_id, choice, updated_at
            FROM preference_responses
            ORDER BY reviewer_code, proposition_id, question_id
            """
        ) if row["reviewer_code"] not in removed_codes]
    metrics = []
    for metric in data.get("rubric", {}).get("metrics", []):
        scores = [int(opt.get("score", 0)) for opt in metric.get("score_options", []) if isinstance(opt.get("score"), int)]
        metrics.append({
            "id": metric.get("id", ""),
            "number": metric.get("number", ""),
            "title": metric.get("title", ""),
            "max_score": max(scores) if scores else 5,
        })
    propositions = []
    for prop in data.get("propositions", []):
        methods = prop.get("methods", {})
        missing_mappings = [
            method_id for method_id, method in methods.items()
            if method.get("available") and not method.get("line_text_mappings")
        ]
        propositions.append({
            "id": prop.get("id", ""),
            "display": prop.get("display", prop.get("id", "")),
            "number": prop.get("number"),
            "title": prop.get("title", ""),
            "ready": bool(methods.get("leaneuclid", {}).get("available") and methods.get("new_method", {}).get("available")),
            "diagram_available": bool(prop.get("diagram", {}).get("available")),
            "missing_mappings": missing_mappings,
        })
    return {
        "methods": data.get("methods", []),
        "metrics": metrics,
        "preference_questions": data.get("preference_questions", {"version": 1, "questions": []}).get("questions", []),
        "preference_choice_scale": {
            "negative_method_id": "leaneuclid",
            "positive_method_id": "new_method",
            "neutral_choice": 0,
        },
        "propositions": propositions,
        "responses": rows,
        "preference_responses": preference_rows,
    }


def export_reviewer_scope(query: dict[str, list[str]]) -> tuple[bool, set[str] | None, str, str]:
    reviewer_scope_param = (query.get("reviewers") or ["all"])[0]
    existing_reviewers_only = reviewer_scope_param == "existing"
    raw_codes = (query.get("reviewer_codes") or [""])[0]
    reviewer_codes = {code.strip() for code in raw_codes.split(",") if code.strip()}
    reviewer_status = (query.get("reviewer_status") or ["all"])[0].strip()
    if reviewer_status not in {"all", "not_started", "in_progress", "done"}:
        reviewer_status = "all"
    if reviewer_scope_param == "active" or reviewer_codes or reviewer_status != "all":
        reviewer_rows = admin_summary_payload().get("reviewers", [])
        allowed = {
            row["reviewer_code"]
            for row in reviewer_rows
            if row.get("active")
            and (not reviewer_codes or row["reviewer_code"] in reviewer_codes)
            and (reviewer_status == "all" or row.get("status") == reviewer_status)
        }
        return True, allowed, reviewer_status, "selected_reviewers" if reviewer_codes else "active_reviewers"
    return existing_reviewers_only, None, reviewer_status, "existing_reviewers" if existing_reviewers_only else "all_reviewers"


def export_rows_as_dicts(
    db: sqlite3.Connection,
    table: str,
    existing_reviewers_only: bool = False,
    reviewer_codes: set[str] | None = None,
) -> list[dict]:
    db.row_factory = sqlite3.Row
    if reviewer_codes is not None:
        if not reviewer_codes:
            rows = []
        else:
            placeholders = ",".join("?" for _ in reviewer_codes)
            rows = [dict(row) for row in db.execute(
                f"""
                SELECT *
                FROM {table}
                WHERE reviewer_code IN ({placeholders})
                ORDER BY reviewer_code, proposition_id
                """,
                tuple(sorted(reviewer_codes)),
            )]
    elif existing_reviewers_only:
        rows = [dict(row) for row in db.execute(
            f"""
            SELECT {table}.*
            FROM {table}
            INNER JOIN reviewers ON reviewers.reviewer_code = {table}.reviewer_code
            LEFT JOIN removed_reviewers ON removed_reviewers.reviewer_code = {table}.reviewer_code
            WHERE removed_reviewers.reviewer_code IS NULL
            ORDER BY {table}.reviewer_code, {table}.proposition_id
            """
        )]
    else:
        rows = [dict(row) for row in db.execute(f"SELECT * FROM {table} ORDER BY reviewer_code, proposition_id")]
    if table == "preference_responses":
        for row in rows:
            row["negative_method_id"] = "leaneuclid"
            row["positive_method_id"] = "new_method"
            choice = row.get("choice")
            row["preferred_method_id"] = "leaneuclid" if isinstance(choice, int) and choice < 0 else ("new_method" if isinstance(choice, int) and choice > 0 else "")
    return rows


def admin_export_payload(
    format_name: str,
    table: str = "responses",
    existing_reviewers_only: bool = False,
    reviewer_codes: set[str] | None = None,
    reviewer_status: str = "all",
    reviewer_scope: str | None = None,
) -> tuple[str, bytes, str]:
    scope = reviewer_scope or ("existing_reviewers" if existing_reviewers_only else "all_reviewers")
    suffix_parts = []
    if scope != "all_reviewers":
        suffix_parts.append(scope)
    if reviewer_status != "all":
        suffix_parts.append(reviewer_status)
    suffix = f"_{'_'.join(suffix_parts)}" if suffix_parts else ""
    with db_connect() as db:
        if format_name == "json":
            payload = {
                "exported_at": now_iso(),
                "survey_version": load_data().get("version", ""),
                "rubric": load_data().get("rubric", {}),
                "preference_questions": load_data().get("preference_questions", {}),
                "preference_choice_scale": {
                    "negative_method_id": "leaneuclid",
                    "positive_method_id": "new_method",
                    "neutral_choice": 0,
                },
                "reviewer_scope": scope,
                "reviewer_status": reviewer_status,
                "reviewer_codes": sorted(reviewer_codes) if reviewer_codes is not None else [],
                "responses": export_rows_as_dicts(db, "responses", existing_reviewers_only, reviewer_codes),
                "preference_responses": export_rows_as_dicts(db, "preference_responses", existing_reviewers_only, reviewer_codes),
                "overall_notes": export_rows_as_dicts(db, "overall_notes", existing_reviewers_only, reviewer_codes),
            }
            body = json.dumps(payload, ensure_ascii=False, indent=2).encode("utf-8") + b"\n"
            return f"responses{suffix}.json", body, "application/json; charset=utf-8"
        rows = export_rows_as_dicts(db, table, existing_reviewers_only, reviewer_codes)
    if table == "overall_notes":
        fieldnames = ["reviewer_code", "proposition_id", "note", "updated_at"]
    elif table == "preference_responses":
        fieldnames = ["reviewer_code", "proposition_id", "question_id", "choice", "negative_method_id", "positive_method_id", "preferred_method_id", "updated_at"]
    elif table == "responses":
        fieldnames = ["reviewer_code", "proposition_id", "method_id", "metric_id", "score", "note", "updated_at"]
    elif rows:
        fieldnames = list(rows[0].keys())
    else:
        fieldnames = []
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=fieldnames)
    writer.writeheader()
    writer.writerows(rows)
    return f"{table}{suffix}.csv", out.getvalue().encode("utf-8"), "text/csv; charset=utf-8"


def system_memory_mb() -> dict:
    info: dict[str, int] = {}
    try:
        for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
            key, raw = line.split(":", 1)
            value = int(raw.strip().split()[0]) // 1024
            info[key] = value
    except Exception:
        return {}
    total = info.get("MemTotal", 0)
    available = info.get("MemAvailable", 0)
    return {
        "total_mb": total,
        "available_mb": available,
        "used_mb": max(0, total - available),
    }


def bytes_to_mb(value: int | None) -> float | None:
    if value is None:
        return None
    return round(value / (1024 * 1024), 1)


def read_int_file(path: Path) -> int | None:
    try:
        raw = path.read_text(encoding="utf-8").strip()
    except Exception:
        return None
    if raw == "max":
        return None
    try:
        return int(raw)
    except ValueError:
        return None


def cgroup_candidates(base: Path, cgroup_path: str) -> list[Path]:
    current = base / cgroup_path.lstrip("/")
    candidates = []
    while True:
        candidates.append(current)
        if current == base or current.parent == current:
            break
        current = current.parent
    return candidates


def first_limited_cgroup(records: list[dict]) -> dict:
    for record in records:
        if record.get("limit_mb") is not None:
            return record
    return records[0] if records else {}


def cgroup_memory_mb(pid: int) -> dict:
    try:
        lines = Path(f"/proc/{pid}/cgroup").read_text(encoding="utf-8").splitlines()
    except Exception:
        return {}

    for line in lines:
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        _, controllers, cgroup_path = parts
        if controllers == "":
            records = []
            for base in cgroup_candidates(Path("/sys/fs/cgroup"), cgroup_path):
                events_path = base / "memory.events"
                events: dict[str, int] = {}
                try:
                    for event_line in events_path.read_text(encoding="utf-8").splitlines():
                        key, value = event_line.split(None, 1)
                        events[key] = int(value)
                except Exception:
                    pass
                current = read_int_file(base / "memory.current")
                if current is None:
                    continue
                limit = read_int_file(base / "memory.max")
                peak = read_int_file(base / "memory.peak")
                records.append({
                    "source": "cgroup v2",
                    "current_mb": bytes_to_mb(current),
                    "limit_mb": bytes_to_mb(limit),
                    "peak_mb": bytes_to_mb(peak),
                    "fail_count": events.get("max"),
                    "oom_kill_count": events.get("oom_kill"),
                })
            return first_limited_cgroup(records)

        if "memory" not in controllers.split(","):
            continue
        records = []
        for base in cgroup_candidates(Path("/sys/fs/cgroup/memory"), cgroup_path):
            current = read_int_file(base / "memory.usage_in_bytes")
            if current is None:
                continue
            limit = read_int_file(base / "memory.limit_in_bytes")
            peak = read_int_file(base / "memory.max_usage_in_bytes")
            # Some hosts expose a huge pseudo-limit when no memory limit is set.
            if limit is not None and limit > 1 << 60:
                limit = None
            oom_kill_count = None
            try:
                for oom_line in (base / "memory.oom_control").read_text(encoding="utf-8").splitlines():
                    if oom_line.startswith("oom_kill "):
                        oom_kill_count = int(oom_line.split()[1])
            except Exception:
                pass
            records.append({
                "source": "cgroup v1",
                "current_mb": bytes_to_mb(current),
                "limit_mb": bytes_to_mb(limit),
                "peak_mb": bytes_to_mb(peak),
                "fail_count": read_int_file(base / "memory.failcnt"),
                "oom_kill_count": oom_kill_count,
            })
        return first_limited_cgroup(records)
    return {}


def process_pss_mb(pid: int) -> float | None:
    try:
        for line in Path(f"/proc/{pid}/smaps_rollup").read_text(encoding="utf-8").splitlines():
            if line.startswith("Pss:"):
                return round(int(line.split()[1]) / 1024, 1)
    except Exception:
        return None
    return None


def process_rows(pids: list[int]) -> list[dict]:
    if not pids:
        return []
    try:
        output = subprocess.check_output(
            ["ps", "-o", "pid=,ppid=,pcpu=,rss=,comm=", "-p", ",".join(str(pid) for pid in pids)],
            text=True,
            stderr=subprocess.DEVNULL,
        )
    except Exception:
        return []
    rows = []
    for line in output.splitlines():
        parts = line.split(None, 4)
        if len(parts) < 5:
            continue
        rows.append({
            "pid": int(parts[0]),
            "ppid": int(parts[1]),
            "cpu_percent": float(parts[2]),
            "rss_mb": round(int(parts[3]) / 1024, 1),
            "pss_mb": process_pss_mb(int(parts[0])),
            "command": parts[4],
        })
    return rows


def resource_snapshot() -> dict:
    pid = os.getpid()
    child_pids = descendant_pids(pid)
    rows = process_rows([pid, *child_pids])
    lean_rows = [row for row in rows if row["command"] == "lean"]
    server_row = next((row for row in rows if row["pid"] == pid), None)
    rows_with_pss = [row for row in rows if row.get("pss_mb") is not None]
    lean_rows_with_pss = [row for row in lean_rows if row.get("pss_mb") is not None]
    try:
        load1, load5, load15 = os.getloadavg()
    except OSError:
        load1 = load5 = load15 = 0.0
    return {
        "server_pid": pid,
        "cpu_count": os.cpu_count() or 0,
        "load_average": {
            "one": round(load1, 2),
            "five": round(load5, 2),
            "fifteen": round(load15, 2),
        },
        "memory": system_memory_mb(),
        "cgroup_memory": cgroup_memory_mb(pid),
        "process_count": len(rows),
        "lean_process_count": len(lean_rows),
        "server_rss_mb": server_row.get("rss_mb", 0) if server_row else 0,
        "server_pss_mb": server_row.get("pss_mb") if server_row else None,
        "server_cpu_percent": server_row.get("cpu_percent", 0) if server_row else 0,
        "total_rss_mb": round(sum(row["rss_mb"] for row in rows), 1),
        "total_pss_mb": round(sum(row["pss_mb"] for row in rows_with_pss), 1) if rows_with_pss else None,
        "total_cpu_percent": round(sum(row["cpu_percent"] for row in rows), 1),
        "lean_rss_mb": round(sum(row["rss_mb"] for row in lean_rows), 1),
        "lean_pss_mb": round(sum(row["pss_mb"] for row in lean_rows_with_pss), 1) if lean_rows_with_pss else None,
        "lean_cpu_percent": round(sum(row["cpu_percent"] for row in lean_rows), 1),
        "top_processes": sorted(rows, key=lambda row: row["rss_mb"], reverse=True)[:8],
    }


def lean_admin_status() -> dict:
    with LEAN_SESSIONS_LOCK:
        session_keys = [
            {"root": root, "file": file_path, "hash": file_hash[:12]}
            for root, file_path, file_hash in LEAN_SESSIONS.keys()
        ]
    session_init = lean_session_init_status()
    with WARM_LOCK:
        warm_requests = [json.loads(json.dumps(WARM_REQUESTS[key])) for key in sorted(WARM_REQUESTS, key=lambda x: int(x))[-10:]]
        return {
            "session_count": len(session_keys),
            "sessions": session_keys,
            "prop_cache_size": PROP_CACHE_SIZE,
            "pinned_warm_prop_ids": sorted(PINNED_WARM_PROP_IDS),
            "prop_client_claim_cap": PROP_CLIENT_CLAIM_CAP,
            "prop_cache_lru": list(PROP_CACHE_LRU),
            "prop_client_claims": {prop_id: sorted(clients) for prop_id, clients in PROP_CLIENT_CLAIMS.items()},
            "client_prop_claims": json.loads(json.dumps(CLIENT_PROP_CLAIMS)),
            "active_prop_id": "",
            "active_props_by_client": dict(CLIENT_ACTIVE_PROP),
            "warm_worker_count": WARM_WORKER_COUNT,
            "warm_queue_size": WARM_QUEUE.qsize(),
            "session_init": session_init,
            "warm_latest_id": WARM_LATEST_ID,
            "warm_requests": warm_requests,
            "resources": resource_snapshot(),
        }


def cancel_all_warmups() -> dict:
    clients: list[LeanLspClient] = []
    keys: list[tuple[str, str, str]] = []
    with WARM_LOCK:
        for req in WARM_REQUESTS.values():
            if req.get("status") in ("queued", "warming"):
                req["status"] = "skipped"
                req["skipped"] = req.get("total", 0)
                req["done"] = req.get("total", 0)
                req["completed_at"] = now_iso()
        for request_id in list(WARM_ACTIVE_CLIENTS):
            clients.extend(WARM_ACTIVE_CLIENTS.pop(request_id, set()))
        for request_id in list(WARM_SESSION_KEYS):
            keys.extend(WARM_SESSION_KEYS.pop(request_id, set()))
    for client in clients:
        client.close()
    with LEAN_SESSIONS_LOCK:
        sessions = [LEAN_SESSIONS.pop(key, None) for key in keys]
    for session in sessions:
        if session is not None:
            session.close()
    return {"ok": True, "closed_clients": len(clients), "closed_sessions": len([s for s in sessions if s is not None])}


def json_response(handler: BaseHTTPRequestHandler, status: int, payload: dict | list) -> None:
    body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json; charset=utf-8")
    handler.send_header("Cache-Control", "no-store")
    handler.send_header("Content-Length", str(len(body)))
    handler.end_headers()
    handler.wfile.write(body)


def text_response(handler: BaseHTTPRequestHandler, status: int, text: str) -> None:
    body = text.encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "text/plain; charset=utf-8")
    handler.send_header("Content-Length", str(len(body)))
    handler.end_headers()
    handler.wfile.write(body)


def find_prop(data: dict, prop_id: str) -> dict | None:
    return next((p for p in data["propositions"] if p["id"] == prop_id), None)


def allowed_file(data: dict, prop_id: str, method_id: str, file_path: str) -> tuple[Path, Path] | None:
    prop = find_prop(data, prop_id)
    if not prop:
        return None
    method = prop["methods"].get(method_id)
    if not method or not method.get("available"):
        return None
    root = resolve_project_root(method["root"])
    for f in method["files"]:
        if f["path"] == file_path:
            full = (root / file_path).resolve()
            try:
                full.relative_to(root)
            except ValueError:
                return None
            return root, full
    candidate = Path(file_path)
    if not candidate.is_absolute():
        candidate = root / file_path
    candidate = candidate.resolve()
    if candidate.exists() and candidate.suffix == ".lean" and any(is_relative_to(candidate, safe_root) for safe_root in safe_source_roots(root)):
        return root, candidate
    return None


def run_lean_state(root: Path, file_path: Path, line: int, column: int = 0, prop_id: str = "", state_request_id: int | None = None, client_id: str = "default") -> dict:
    rel = display_file_path(root, file_path)

    source_lines = file_path.read_text(encoding="utf-8").splitlines()
    if source_lines:
        line = max(1, min(line, len(source_lines)))
        column = max(0, min(column, len(source_lines[line - 1])))
    else:
        line = 1
        column = 0
    lo = max(1, line - 4)
    hi = min(len(source_lines), line + 4)
    context = [{"line": i, "text": source_lines[i - 1]} for i in range(lo, hi + 1)]

    payload = {
        "available": False,
        "mode": "diagnostics",
        "file": rel,
        "line": line,
        "column": column,
        "rpcSessionId": None,
        "context": context,
        "messages": [],
        "allMessages": [],
        "goal": "",
        "goals": [],
        "goalCount": 0,
        "termGoal": None,
        "interactiveMessages": [],
        "allInteractiveMessages": [],
        "rpcErrors": [],
        "status": "fallback",
        "note": "Live Lean goals require the Lean RPC worker. This endpoint currently returns checked diagnostics and source context.",
    }

    rpc_failed = False
    if os.environ.get("LEAN_SURVEY_DISABLE_RPC", "").lower() not in ("1", "true", "yes"):
        try:
            payload = run_lean_rpc_state(root, file_path, line, column, context, prop_id, state_request_id, client_id)
            return payload
        except TimeoutError as exc:
            if "stale Lean" in str(exc):
                raise
            rpc_failed = True
            payload["note"] = f"Lean RPC goal query timed out; showing cached diagnostics only. {exc}"
        except Exception as exc:
            if "stale Lean" in str(exc):
                raise
            rpc_failed = True
            payload["note"] = f"Lean RPC goal query failed; showing diagnostics fallback. {exc}"

    if rpc_failed:
        return payload

    try:
        ensure_current_prop(prop_id, client_id)
        proc = subprocess.run(
            ["lake", "env", "lean", "--json", rel],
            cwd=root,
            env=lean_direct_env(root),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=int(os.environ.get("LEAN_SURVEY_TIMEOUT", "25")),
        )
        messages = []
        for raw in proc.stdout.splitlines():
            raw = raw.strip()
            if not raw:
                continue
            try:
                msg = json.loads(raw)
            except json.JSONDecodeError:
                continue
            pos = msg.get("pos") or {}
            end_pos = msg.get("endPos") or {}
            if not pos or abs(int(pos.get("line", line)) - line) <= 8:
                messages.append({
                    "severity": msg.get("severity", "info"),
                    "line": pos.get("line"),
                    "column": pos.get("column"),
                    "endLine": end_pos.get("line"),
                    "message": msg.get("data", ""),
                })
        payload.update({
            "available": proc.returncode == 0 or bool(messages),
            "messages": messages,
            "allMessages": messages,
            "stderr": proc.stderr[-2000:],
            "exitCode": proc.returncode,
        })
    except subprocess.TimeoutExpired:
        payload["note"] = "Lean check timed out. Try a nearby line or ensure the project is already built on a compute node."
    except Exception as exc:
        payload["note"] = f"Lean check failed: {exc}"

    return payload


def warm_request_snapshot(request_id: str) -> dict | None:
    with WARM_LOCK:
        item = WARM_REQUESTS.get(str(request_id))
        return json.loads(json.dumps(item)) if item else None


def close_prop_sessions(prop_id: str) -> None:
    clients: list[LeanLspClient] = []
    keys: list[tuple[str, str, str]] = []
    with WARM_LOCK:
        clients.extend(PROP_ACTIVE_CLIENTS.pop(prop_id, set()))
        keys.extend(PROP_SESSION_KEYS.pop(prop_id, set()))

    for client in clients:
        client.close()

    sessions: list[LeanFileSession] = []
    with LEAN_SESSIONS_LOCK:
        for key in keys:
            session = LEAN_SESSIONS.pop(key, None)
            if session is not None:
                sessions.append(session)
    for session in sessions:
        session.close()


def remove_prop_claims_locked(prop_id: str) -> None:
    prop_id = str(prop_id)
    clients = PROP_CLIENT_CLAIMS.pop(prop_id, set())
    for client_id in clients:
        claims = CLIENT_PROP_CLAIMS.get(client_id)
        if claims is None:
            continue
        CLIENT_PROP_CLAIMS[client_id] = [item for item in claims if item != prop_id]
        if not CLIENT_PROP_CLAIMS[client_id]:
            CLIENT_PROP_CLAIMS.pop(client_id, None)


def real_claim_client_ids(client_ids) -> list[str]:
    clean: list[str] = []
    for client_id in client_ids or []:
        client_id = str(client_id or "").strip()
        if not client_id or client_id.startswith("warm:") or client_id in clean:
            continue
        clean.append(client_id)
    return clean


def add_prop_claim_locked(client_id: str, prop_id: str) -> list[str]:
    client_id = lean_client_id(client_id)
    prop_id = str(prop_id)
    evicted: list[str] = []
    claims = CLIENT_PROP_CLAIMS.setdefault(client_id, [])
    if prop_id in claims:
        claims.remove(prop_id)
    claims.append(prop_id)
    PROP_CLIENT_CLAIMS.setdefault(prop_id, set()).add(client_id)
    while len(claims) > max(1, PROP_CLIENT_CLAIM_CAP):
        old_prop_id = claims.pop(0)
        prop_clients = PROP_CLIENT_CLAIMS.get(old_prop_id)
        if prop_clients is not None:
            prop_clients.discard(client_id)
            if not prop_clients:
                PROP_CLIENT_CLAIMS.pop(old_prop_id, None)
                if old_prop_id in PROP_CACHE_LRU:
                    PROP_CACHE_LRU.remove(old_prop_id)
                    evicted.append(old_prop_id)
    return evicted


def touch_prop_cache(prop_id: str, client_ids=None) -> None:
    evicted: list[str] = []
    if not prop_id:
        return
    claim_client_ids = real_claim_client_ids(client_ids)
    with WARM_LOCK:
        if prop_id in PROP_CACHE_LRU:
            PROP_CACHE_LRU.remove(prop_id)
        PROP_CACHE_LRU.append(prop_id)
        for client_id in claim_client_ids:
            evicted.extend(add_prop_claim_locked(client_id, prop_id))
        while len(PROP_CACHE_LRU) > max(1, PROP_CACHE_SIZE):
            old_prop_id = next(
                (item for item in PROP_CACHE_LRU if item not in PINNED_WARM_PROP_IDS and not PROP_CLIENT_CLAIMS.get(item)),
                "",
            )
            if not old_prop_id:
                old_prop_id = next((item for item in PROP_CACHE_LRU if item not in PINNED_WARM_PROP_IDS), "")
            if not old_prop_id:
                break
            PROP_CACHE_LRU.remove(old_prop_id)
            remove_prop_claims_locked(old_prop_id)
            evicted.append(old_prop_id)
        evicted = list(dict.fromkeys(evicted))
    for old_prop_id in evicted:
        close_prop_sessions(old_prop_id)


def set_client_active_prop(client_id: str, prop_id: str) -> None:
    client_id = lean_client_id(client_id)
    with WARM_LOCK:
        CLIENT_ACTIVE_PROP[client_id] = str(prop_id)


def clear_client_active_prop(client_id: str) -> None:
    client_id = lean_client_id(client_id)
    with WARM_LOCK:
        CLIENT_ACTIVE_PROP.pop(client_id, None)


def sync_warm_request_claims_locked(req: dict) -> None:
    client_claims = req.get("attached_client_claims")
    if isinstance(client_claims, dict):
        req["attached_clients"] = sorted(client_claims)
        req["attached_claim_ids"] = sorted({str(claim_id) for claim_id in client_claims.values() if claim_id})
    else:
        clients = set(req.get("attached_clients") or [req.get("client_id", "")])
        req["attached_clients"] = sorted(item for item in clients if item)
        claims = set(req.get("attached_claim_ids") or [req.get("claim_id", "")])
        req["attached_claim_ids"] = sorted(item for item in claims if item)


def detach_warm_client_locked(req: dict, client_id: str) -> None:
    client_id = lean_client_id(client_id)
    client_claims = req.get("attached_client_claims")
    if isinstance(client_claims, dict):
        client_claims.pop(client_id, None)
    attached = set(req.get("attached_clients") or [req.get("client_id", "")])
    attached.discard(client_id)
    req["attached_clients"] = sorted(item for item in attached if item)
    sync_warm_request_claims_locked(req)


def detach_warm_claim_locked(req: dict, claim_id: str) -> list[str]:
    claim_id = str(claim_id or "").strip()
    removed_clients: list[str] = []
    client_claims = req.get("attached_client_claims")
    if isinstance(client_claims, dict):
        for client_id, attached_claim_id in list(client_claims.items()):
            if attached_claim_id == claim_id:
                removed_clients.append(client_id)
                client_claims.pop(client_id, None)
    elif claim_id in set(req.get("attached_claim_ids") or [req.get("claim_id", "")]):
        removed_clients = list(req.get("attached_clients") or [req.get("client_id", "")])
        req["attached_clients"] = []
        req["attached_claim_ids"] = []
    sync_warm_request_claims_locked(req)
    return removed_clients


def warm_request_has_active_client_locked(req: dict) -> bool:
    prop_id = str(req.get("proposition_id", ""))
    for client_id in req.get("attached_clients") or []:
        if CLIENT_ACTIVE_PROP.get(lean_client_id(client_id)) == prop_id:
            return True
    return False


def skip_warm_request_locked(request_id: str, req: dict, canceled: set[str]) -> None:
    req["status"] = "skipped"
    req["skipped"] = req.get("total", 0)
    req["done"] = req.get("total", 0)
    req["completed_at"] = now_iso()
    canceled.add(request_id)
    prop_id = str(req.get("proposition_id", ""))
    if prop_id and WARM_INFLIGHT_BY_PROP.get(prop_id) == request_id:
        WARM_INFLIGHT_BY_PROP.pop(prop_id, None)


def ensure_warm_request_has_active_client(request_id: str, prop_id: str) -> None:
    prop_id = str(prop_id)
    with WARM_LOCK:
        req = WARM_REQUESTS.get(str(request_id))
        if not req or req.get("status") == "skipped":
            raise StaleWarmRequest("stale Lean warm-up skipped")
        if warm_request_has_active_client_locked(req):
            return
    raise StaleWarmRequest("stale Lean warm-up skipped because no attached reviewer is still on this proposition")


def cancel_superseded_warmups(latest_request_id: str, client_id: str = "default") -> None:
    client_id = lean_client_id(client_id)
    clients: list[LeanLspClient] = []
    keys: list[tuple[str, str, str]] = []
    canceled: set[str] = set()
    with WARM_LOCK:
        for request_id, req in WARM_REQUESTS.items():
            if request_id == latest_request_id:
                continue
            if req.get("status") not in ("queued", "warming"):
                continue
            attached = set(req.get("attached_clients") or [req.get("client_id", "")])
            if client_id not in attached:
                continue
            detach_warm_client_locked(req, client_id)
            if warm_request_has_active_client_locked(req):
                continue
            else:
                skip_warm_request_locked(request_id, req, canceled)
        for request_id in list(WARM_ACTIVE_CLIENTS):
            if request_id in canceled:
                clients.extend(WARM_ACTIVE_CLIENTS.pop(request_id, set()))
        for request_id in list(WARM_SESSION_KEYS):
            if request_id in canceled:
                keys.extend(WARM_SESSION_KEYS.pop(request_id, set()))

    for client in clients:
        client.close()

    sessions: list[LeanFileSession] = []
    with LEAN_SESSIONS_LOCK:
        for key in keys:
            session = LEAN_SESSIONS.pop(key, None)
            if session is not None:
                sessions.append(session)
    for session in sessions:
        session.close()


def enforce_warm_claim_cap(claim_id: str, keep_request_id: str) -> None:
    claim_id = str(claim_id or "").strip()
    if not claim_id:
        return
    clients: list[LeanLspClient] = []
    keys: list[tuple[str, str, str]] = []
    canceled: set[str] = set()
    with WARM_LOCK:
        matching: list[tuple[int, str, dict]] = []
        for request_id, req in WARM_REQUESTS.items():
            if req.get("status") not in ("queued", "warming"):
                continue
            claims = set(req.get("attached_claim_ids") or [req.get("claim_id", "")])
            if claim_id not in claims:
                continue
            try:
                order = int(request_id)
            except ValueError:
                order = 0
            matching.append((order, request_id, req))
        matching.sort()
        excess = len(matching) - max(1, PROP_CLIENT_CLAIM_CAP)
        if excess <= 0:
            return
        for _, request_id, req in matching:
            if excess <= 0:
                break
            if request_id == keep_request_id:
                continue
            detach_warm_claim_locked(req, claim_id)
            excess -= 1
            if not warm_request_has_active_client_locked(req):
                skip_warm_request_locked(request_id, req, canceled)
        for request_id in list(WARM_ACTIVE_CLIENTS):
            if request_id in canceled:
                clients.extend(WARM_ACTIVE_CLIENTS.pop(request_id, set()))
        for request_id in list(WARM_SESSION_KEYS):
            if request_id in canceled:
                keys.extend(WARM_SESSION_KEYS.pop(request_id, set()))

    for client in clients:
        client.close()

    sessions: list[LeanFileSession] = []
    with LEAN_SESSIONS_LOCK:
        for key in keys:
            session = LEAN_SESSIONS.pop(key, None)
            if session is not None:
                sessions.append(session)
    for session in sessions:
        session.close()


def finish_warm_job(request_id: str, warmed: dict | None = None, error: dict | None = None, skipped: bool = False) -> None:
    ready_prop_id = ""
    ready_client_ids: list[str] = []
    with WARM_LOCK:
        req = WARM_REQUESTS.get(request_id)
        if not req:
            return
        if req.get("status") == "skipped" and req.get("done", 0) >= req.get("total", 0):
            return
        if warmed:
            req["warmed"].append(warmed)
        if error:
            req["errors"].append(error)
        if skipped:
            req["skipped"] += 1
        req["done"] += 1
        if req["done"] >= req["total"]:
            prop_id = str(req.get("proposition_id", ""))
            if prop_id and WARM_INFLIGHT_BY_PROP.get(prop_id) == request_id:
                WARM_INFLIGHT_BY_PROP.pop(prop_id, None)
            if req["errors"] and req["warmed"]:
                req["status"] = "partial"
                ready_prop_id = str(req.get("proposition_id", ""))
                ready_client_ids = list(req.get("attached_claim_ids") or [req.get("claim_id", "")])
            elif req["errors"]:
                req["status"] = "failed"
            elif req["skipped"] == req["total"]:
                req["status"] = "skipped"
            else:
                req["status"] = "ready"
                ready_prop_id = str(req.get("proposition_id", ""))
                ready_client_ids = list(req.get("attached_claim_ids") or [req.get("claim_id", "")])
            req["completed_at"] = now_iso()
    if ready_prop_id:
        touch_prop_cache(ready_prop_id, ready_client_ids)


def warm_worker() -> None:
    while True:
        job = WARM_QUEUE.get()
        try:
            request_id = str(job.get("request_id", ""))
            with WARM_LOCK:
                req = WARM_REQUESTS.get(request_id)
                should_skip = not req or req.get("status") == "skipped"
                if req and req["status"] == "queued":
                    req["status"] = "warming"
            if should_skip:
                finish_warm_job(request_id, skipped=True)
                continue

            data = load_data()
            prop_id = str(job.get("proposition_id", ""))
            method_id = str(job.get("method_id", ""))
            file_path = str(job.get("file_path", ""))
            warm_client_id = f"warm:{request_id}"
            set_client_active_prop(warm_client_id, prop_id)
            cancel_check = lambda: ensure_warm_request_has_active_client(request_id, prop_id)
            cancel_check()
            allowed = allowed_file(data, prop_id, method_id, file_path)
            if not allowed:
                finish_warm_job(request_id, error={
                    "method_id": method_id,
                    "file_path": file_path,
                    "error": "file is not an allowed survey or dependency source",
                })
                continue
            root, full = allowed
            file_hash = hashlib.sha256(full.read_bytes()).hexdigest()
            session = get_lean_session(root, full, file_hash, prop_id, request_id, cancel_check=cancel_check, client_id=warm_client_id, priority="background")
            finish_warm_job(request_id, warmed={
                "method_id": method_id,
                "file_path": file_path,
                "ready_at": session.ready_at,
            })
        except StaleWarmRequest:
            finish_warm_job(str(job.get("request_id", "")), skipped=True)
        except Exception as exc:
            finish_warm_job(str(job.get("request_id", "")), error={
                "method_id": str(job.get("method_id", "")),
                "file_path": str(job.get("file_path", "")),
                "error": str(exc),
            })
        finally:
            request_id = str(job.get("request_id", ""))
            if request_id:
                clear_client_active_prop(f"warm:{request_id}")
            WARM_QUEUE.task_done()


def start_warm_workers() -> None:
    global WARM_WORKERS_STARTED
    if WARM_WORKERS_STARTED:
        return
    WARM_WORKERS_STARTED = True
    for idx in range(max(1, WARM_WORKER_COUNT)):
        threading.Thread(target=warm_worker, name=f"lean-warm-{idx + 1}", daemon=True).start()


def enqueue_startup_pinned_warmups(data: dict) -> None:
    if os.environ.get("LEAN_SURVEY_DISABLE_RPC", "").lower() in ("1", "true", "yes"):
        return
    if not PINNED_WARM_PROP_IDS:
        return
    props = {str(prop.get("id", "")): prop for prop in data.get("propositions", [])}
    for prop_id in sorted(PINNED_WARM_PROP_IDS):
        prop = props.get(prop_id)
        if not prop:
            continue
        files = []
        for method_id in ("leaneuclid", "new_method"):
            method = prop.get("methods", {}).get(method_id, {})
            file = next(iter(method.get("files", []) or []), None)
            if file and file.get("path"):
                files.append({"method_id": method_id, "file_path": file["path"]})
        if files:
            enqueue_warm_request(prop_id, files, client_id=f"startup:{prop_id}")


def prop_cached(prop_id: str) -> bool:
    with WARM_LOCK:
        return str(prop_id) in PROP_CACHE_LRU


def enqueue_warm_request(prop_id: str, files: list[dict], client_id: str = "default", reviewer_code: str = "") -> dict:
    global WARM_LATEST_ID
    prop_id = str(prop_id)
    client_id = lean_client_id(client_id)
    claim_id = lean_claim_id(reviewer_code, client_id)
    set_client_active_prop(client_id, prop_id)
    if prop_cached(prop_id):
        touch_prop_cache(prop_id, [claim_id])
        return {
            "request_id": "",
            "proposition_id": prop_id,
            "client_id": client_id,
            "claim_id": claim_id,
            "status": "ready",
            "total": len(files),
            "done": len(files),
            "skipped": 0,
            "warmed": [],
            "errors": [],
            "created_at": now_iso(),
            "completed_at": now_iso(),
        }
    attached_snapshot = None
    attached_request_id = ""
    cancel_after_lock = False
    with WARM_LOCK:
        existing_id = WARM_INFLIGHT_BY_PROP.get(prop_id)
        if existing_id:
            existing = WARM_REQUESTS.get(existing_id)
            if existing and existing.get("status") in ("queued", "warming"):
                client_claims = existing.get("attached_client_claims")
                if not isinstance(client_claims, dict):
                    client_claims = {
                        attached_client_id: existing.get("claim_id", "")
                        for attached_client_id in existing.get("attached_clients") or [existing.get("client_id", "")]
                        if attached_client_id
                    }
                    existing["attached_client_claims"] = client_claims
                client_claims[client_id] = claim_id
                sync_warm_request_claims_locked(existing)
                CLIENT_LATEST_WARM_ID[client_id] = existing_id
                attached_request_id = existing_id
                attached_snapshot = json.loads(json.dumps(existing))

        if attached_snapshot is None:
            WARM_LATEST_ID += 1
            request_id = str(WARM_LATEST_ID)
            WARM_REQUESTS[request_id] = {
                "request_id": request_id,
                "proposition_id": prop_id,
                "client_id": client_id,
                "claim_id": claim_id,
                "attached_clients": [client_id],
                "attached_claim_ids": [claim_id],
                "attached_client_claims": {client_id: claim_id},
                "status": "ready" if not files else "queued",
                "total": len(files),
                "done": 0,
                "skipped": 0,
                "warmed": [],
                "errors": [],
                "created_at": now_iso(),
                "completed_at": now_iso() if not files else "",
            }
            CLIENT_LATEST_WARM_ID[client_id] = request_id
            if files:
                WARM_INFLIGHT_BY_PROP[prop_id] = request_id
            cancel_after_lock = bool(files)
            protected_ids = {request_id, *WARM_INFLIGHT_BY_PROP.values()}
            for old_id in sorted(WARM_REQUESTS, key=lambda x: int(x))[:-25]:
                old_req = WARM_REQUESTS.get(old_id) or {}
                if old_id in protected_ids or old_req.get("status") in ("queued", "warming"):
                    continue
                WARM_REQUESTS.pop(old_id, None)
        else:
            request_id = attached_request_id
            cancel_after_lock = True
    if cancel_after_lock:
        cancel_superseded_warmups(request_id, client_id)
        enforce_warm_claim_cap(claim_id, request_id)
    if attached_snapshot is not None:
        return attached_snapshot
    for item in files:
        WARM_QUEUE.put({
            "request_id": request_id,
            "proposition_id": prop_id,
            "client_id": client_id,
            "method_id": str(item.get("method_id", "")),
            "file_path": str(item.get("file_path", "")),
        })
    return warm_request_snapshot(request_id) or {"request_id": request_id, "status": "queued"}


class SurveyHandler(BaseHTTPRequestHandler):
    server_version = "FaithfulnessSurvey/0.1"

    def admin_token(self) -> str:
        return parse_cookies(self.headers.get("Cookie", "")).get("survey_admin", "")

    def is_admin(self) -> bool:
        return admin_session_valid(self.admin_token())

    def require_admin(self) -> bool:
        if self.is_admin():
            return True
        json_response(self, 401, {"error": "admin authentication required"})
        return False

    def send_download(self, filename: str, body: bytes, content_type: str) -> None:
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Disposition", f'attachment; filename="{filename}"')
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)
        try:
            if path == "/admin" or path.startswith("/admin/"):
                return self.serve_admin_static(path)
            if path == "/api/admin/session":
                return json_response(self, 200, {
                    "authenticated": self.is_admin(),
                    "configured": admin_secret_configured(),
                })
            if path.startswith("/api/admin/"):
                if not self.require_admin():
                    return
                if path == "/api/admin/summary":
                    return json_response(self, 200, admin_summary_payload())
                if path == "/api/admin/scores":
                    return json_response(self, 200, admin_scores_payload())
                if path == "/api/admin/lean/status":
                    return json_response(self, 200, lean_admin_status())
                if path == "/api/admin/exports/responses.json":
                    existing_only, reviewer_codes, reviewer_status, reviewer_scope = export_reviewer_scope(query)
                    filename, body, content_type = admin_export_payload(
                        "json",
                        existing_reviewers_only=existing_only,
                        reviewer_codes=reviewer_codes,
                        reviewer_status=reviewer_status,
                        reviewer_scope=reviewer_scope,
                    )
                    audit_admin("export", filename)
                    return self.send_download(filename, body, content_type)
                if path == "/api/admin/exports/responses.csv":
                    existing_only, reviewer_codes, reviewer_status, reviewer_scope = export_reviewer_scope(query)
                    filename, body, content_type = admin_export_payload(
                        "csv",
                        "responses",
                        existing_reviewers_only=existing_only,
                        reviewer_codes=reviewer_codes,
                        reviewer_status=reviewer_status,
                        reviewer_scope=reviewer_scope,
                    )
                    audit_admin("export", filename)
                    return self.send_download(filename, body, content_type)
                if path == "/api/admin/exports/overall_notes.csv":
                    existing_only, reviewer_codes, reviewer_status, reviewer_scope = export_reviewer_scope(query)
                    filename, body, content_type = admin_export_payload(
                        "csv",
                        "overall_notes",
                        existing_reviewers_only=existing_only,
                        reviewer_codes=reviewer_codes,
                        reviewer_status=reviewer_status,
                        reviewer_scope=reviewer_scope,
                    )
                    audit_admin("export", filename)
                    return self.send_download(filename, body, content_type)
                if path == "/api/admin/exports/preference_responses.csv":
                    existing_only, reviewer_codes, reviewer_status, reviewer_scope = export_reviewer_scope(query)
                    filename, body, content_type = admin_export_payload(
                        "csv",
                        "preference_responses",
                        existing_reviewers_only=existing_only,
                        reviewer_codes=reviewer_codes,
                        reviewer_status=reviewer_status,
                        reviewer_scope=reviewer_scope,
                    )
                    audit_admin("export", filename)
                    return self.send_download(filename, body, content_type)
                return json_response(self, 404, {"error": "unknown admin endpoint"})
            if path == "/api/config":
                data = load_data()
                return json_response(self, 200, {
                    "version": data["version"],
                    "methods": data["methods"],
                    "rubric": data["rubric"],
                    "preference_questions": data.get("preference_questions", {"version": 1, "questions": []}),
                    "references": data.get("references", {}),
                })
            if path == "/api/propositions":
                data = load_data()
                props = []
                for p in data["propositions"]:
                    props.append({
                        "id": p["id"],
                        "book": p["book"],
                        "number": p["number"],
                        "display": p["display"],
                        "title": p["title"],
                        "diagram": p["diagram"],
                        "methodAvailability": {k: v["available"] for k, v in p["methods"].items()},
                    })
                return json_response(self, 200, props)
            if path.startswith("/api/propositions/"):
                prop_id = unquote(path.rsplit("/", 1)[-1])
                prop = find_prop(load_data(), prop_id)
                return json_response(self, 200, prop) if prop else json_response(self, 404, {"error": "unknown proposition"})
            if path.startswith("/api/reviewers/"):
                reviewer = unquote(path.rsplit("/", 1)[-1]).strip()
                exists = reviewer_exists(reviewer)
                status = 200 if exists else 404
                return json_response(self, status, {"reviewer_code": reviewer, "exists": exists})
            if path.startswith("/api/invites/"):
                token = unquote(path.rsplit("/", 1)[-1]).strip()
                reviewer = reviewer_code_for_token(token)
                if not reviewer:
                    return json_response(self, 404, {"error": "unknown or disabled reviewer link"})
                return json_response(self, 200, {"ok": True})
            if path.startswith("/api/progress-token/"):
                token = unquote(path.rsplit("/", 1)[-1]).strip()
                reviewer = reviewer_code_for_token(token)
                if not reviewer:
                    return json_response(self, 404, {"error": "unknown or disabled reviewer link"})
                return json_response(self, 200, reviewer_progress_payload(reviewer))
            if path.startswith("/api/progress/"):
                reviewer = unquote(path.rsplit("/", 1)[-1]).strip()
                if not reviewer_exists(reviewer):
                    return json_response(self, 404, {"error": "unknown reviewer_code"})
                return json_response(self, 200, reviewer_progress_payload(reviewer, include_code=True))
            if path.startswith("/api/tutorial-token/"):
                token = unquote(path.rsplit("/", 1)[-1]).strip()
                reviewer = reviewer_code_for_token(token)
                if not reviewer:
                    return json_response(self, 404, {"error": "unknown or disabled reviewer link"})
                return json_response(self, 200, reviewer_tutorial_payload(reviewer))
            if path.startswith("/api/tutorial/"):
                reviewer = unquote(path.rsplit("/", 1)[-1]).strip()
                if not reviewer_exists(reviewer):
                    return json_response(self, 404, {"error": "unknown reviewer_code"})
                return json_response(self, 200, reviewer_tutorial_payload(reviewer, include_code=True))
            if path.startswith("/api/assets/diagrams/"):
                name = Path(unquote(path.rsplit("/", 1)[-1])).name
                asset = LEANEUCLID_PLUS / "Book1" / "data" / "diagrams" / name
                if asset.exists() and asset.suffix == ".png":
                    body = asset.read_bytes()
                    self.send_response(200)
                    self.send_header("Content-Type", "image/png")
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                    return
                return json_response(self, 404, {"error": "asset not found"})
            return self.serve_static(path)
        except Exception as exc:
            return json_response(self, 500, {"error": str(exc)})

    def do_POST(self) -> None:
        parsed = urlparse(self.path)
        try:
            length = int(self.headers.get("Content-Length", "0"))
            payload = json.loads(self.rfile.read(length).decode("utf-8") or "{}")
            if parsed.path == "/api/admin/login":
                return self.admin_login(payload)
            if parsed.path == "/api/admin/logout":
                return self.admin_logout()
            if parsed.path.startswith("/api/admin/"):
                if not self.require_admin():
                    return
                if parsed.path == "/api/admin/reviewers":
                    return self.admin_add_reviewer(payload)
                if parsed.path == "/api/admin/reviewers/invite":
                    return self.admin_invite_reviewer(payload)
                if parsed.path == "/api/admin/reviewers/disable":
                    return self.admin_disable_reviewer(payload)
                if parsed.path == "/api/admin/reviewers/remove":
                    return self.admin_remove_reviewer(payload)
                if parsed.path == "/api/admin/lean/clear-cache":
                    cancel_all_warmups()
                    prop_clients: list[LeanLspClient] = []
                    with WARM_LOCK:
                        for prop_id in list(PROP_ACTIVE_CLIENTS):
                            prop_clients.extend(PROP_ACTIVE_CLIENTS.pop(prop_id, set()))
                        PROP_CACHE_LRU.clear()
                        PROP_CLIENT_CLAIMS.clear()
                        CLIENT_PROP_CLAIMS.clear()
                        PROP_SESSION_KEYS.clear()
                    for client in prop_clients:
                        client.close()
                    close_lean_sessions()
                    audit_admin("lean.clear_cache")
                    return json_response(self, 200, {"ok": True, "closed_clients": len(prop_clients)})
                if parsed.path == "/api/admin/lean/cancel-warmups":
                    result = cancel_all_warmups()
                    audit_admin("lean.cancel_warmups")
                    return json_response(self, 200, result)
                return json_response(self, 404, {"error": "unknown admin endpoint"})
            if parsed.path == "/api/responses":
                return self.save_response(payload)
            if parsed.path == "/api/tutorial":
                return self.save_tutorial(payload)
            if parsed.path == "/api/reviewer-links":
                return self.public_reviewer_link(payload)
            if parsed.path == "/api/lean/state":
                return self.lean_state(payload)
            if parsed.path == "/api/lean/hover":
                return self.lean_hover(payload)
            if parsed.path == "/api/lean/definition":
                return self.lean_definition(payload)
            if parsed.path == "/api/lean/info-hover":
                return self.lean_info_hover(payload)
            if parsed.path == "/api/lean/trace-children":
                return self.lean_trace_children(payload)
            if parsed.path == "/api/lean/warm":
                return self.lean_warm(payload)
            if parsed.path == "/api/lean/warm-status":
                return self.lean_warm_status(payload)
            return json_response(self, 404, {"error": "unknown endpoint"})
        except json.JSONDecodeError:
            return json_response(self, 400, {"error": "invalid json"})
        except RuntimeError as exc:
            if "stale Lean" in str(exc):
                return json_response(self, 409, {"error": str(exc), "stale": True})
            return json_response(self, 500, {"error": str(exc)})
        except Exception as exc:
            return json_response(self, 500, {"error": str(exc)})

    def admin_login(self, payload: dict) -> None:
        if not admin_secret_configured():
            audit_admin("login_failed", "admin secret not configured")
            return json_response(self, 503, {"error": "admin login is not configured"})
        password = str(payload.get("password", ""))
        if not verify_admin_secret(password):
            audit_admin("login_failed", self.client_address[0] if self.client_address else "")
            return json_response(self, 403, {"error": "invalid admin password"})
        token = create_admin_session()
        body = json.dumps({"ok": True}).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Set-Cookie", f"survey_admin={quote(token)}; Max-Age={max(300, ADMIN_SESSION_SECONDS)}; HttpOnly; SameSite=Lax; Path=/")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
        audit_admin("login")

    def admin_logout(self) -> None:
        destroy_admin_session(self.admin_token())
        body = json.dumps({"ok": True}).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Set-Cookie", "survey_admin=; Max-Age=0; HttpOnly; SameSite=Lax; Path=/")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)
        audit_admin("logout")

    def admin_add_reviewer(self, payload: dict) -> None:
        code = str(payload.get("reviewer_code", "")).strip()
        if not code:
            return json_response(self, 400, {"error": "reviewer_code required"})
        ts = now_iso()
        with db_connect() as db:
            db.execute("DELETE FROM removed_reviewers WHERE reviewer_code = ?", (code,))
            db.execute(
                """
                INSERT INTO reviewers (reviewer_code, created_at, disabled_at)
                VALUES (?, ?, '')
                ON CONFLICT(reviewer_code)
                DO UPDATE SET disabled_at = ''
                """,
                (code, ts),
            )
            db.commit()
        audit_admin("reviewer.add", code)
        return json_response(self, 200, {"ok": True, "reviewer_code": code})

    def send_reviewer_link(self, email: str, access_url: str, is_public: bool = False) -> dict:
        email = str(email or "").strip()
        normalized = normalize_email(email)
        if not valid_email(email):
            raise ValueError("valid email required")
        access_url = public_access_url(self, access_url)
        ts = now_iso()
        created = False
        with db_connect() as db:
            row = db.execute(
                """
                SELECT reviewer_code, invite_token, sent_at
                FROM reviewer_invites
                WHERE email_normalized = ?
                """,
                (normalized,),
            ).fetchone()
            if row:
                code, token, sent_at = row
                db.execute("DELETE FROM removed_reviewers WHERE reviewer_code = ?", (code,))
                db.execute(
                    """
                    INSERT INTO reviewers (reviewer_code, created_at, disabled_at)
                    VALUES (?, ?, '')
                    ON CONFLICT(reviewer_code)
                    DO UPDATE SET disabled_at = ''
                    """,
                    (code, ts),
                )
                if is_public and sent_at:
                    sent_epoch = iso_z_epoch(sent_at)
                    if sent_epoch and time.time() - sent_epoch < max(0, INVITE_RESEND_COOLDOWN_SECONDS):
                        raise TimeoutError("an instruction email was sent recently; please check your inbox or try again later")
                if not token:
                    token = generate_invite_token(db)
                    db.execute(
                        "UPDATE reviewer_invites SET invite_token = ? WHERE reviewer_code = ?",
                        (token, code),
                    )
            else:
                code = generate_reviewer_code(db)
                token = generate_invite_token(db)
                db.execute(
                    """
                    INSERT INTO reviewers (reviewer_code, created_at, disabled_at)
                    VALUES (?, ?, '')
                    """,
                    (code, ts),
                )
                db.execute(
                    """
                    INSERT INTO reviewer_invites (reviewer_code, email, email_normalized, access_url, invite_token, created_at, sent_at)
                    VALUES (?, ?, ?, ?, ?, ?, '')
                    """,
                    (code, email, normalized, access_url, token, ts),
                )
                created = True
            db.commit()
        try:
            send_invite_email(
                email,
                "Faithfulness Survey personal link",
                reviewer_invite_body(access_url, token),
            )
        except Exception:
            if created:
                with db_connect() as db:
                    db.execute("DELETE FROM reviewer_invites WHERE reviewer_code = ?", (code,))
                    db.execute("DELETE FROM reviewers WHERE reviewer_code = ?", (code,))
                    db.commit()
            raise
        with db_connect() as db:
            db.execute(
                """
                UPDATE reviewer_invites
                SET email = ?, email_normalized = ?, access_url = ?, invite_token = ?, sent_at = ?
                WHERE reviewer_code = ?
                """,
                (email, normalized, access_url, token, ts, code),
            )
            db.commit()
        return {
            "reviewer_code": code,
            "email": email,
            "sent_at": ts,
            "access_url": access_url,
            "invite_url": reviewer_link(access_url, token),
        }

    def public_reviewer_link(self, payload: dict) -> None:
        ip = self.client_address[0] if self.client_address else "unknown"
        if not rate_limit_reviewer_link(ip):
            return json_response(self, 429, {"error": "too many email requests; please try again later"})
        try:
            result = self.send_reviewer_link(str(payload.get("email", "")), "", is_public=True)
        except ValueError as exc:
            return json_response(self, 400, {"error": str(exc)})
        except TimeoutError as exc:
            return json_response(self, 429, {"error": str(exc)})
        except Exception as exc:
            audit_admin("reviewer.self_invite_failed", str(exc))
            return json_response(self, 500, {"error": f"email send failed: {exc}"})
        audit_admin("reviewer.self_invite", result["email"])
        return json_response(self, 200, {"ok": True, "sent_at": result["sent_at"]})

    def admin_invite_reviewer(self, payload: dict) -> None:
        try:
            result = self.send_reviewer_link(
                str(payload.get("email", "")),
                str(payload.get("access_url", "")),
                is_public=False,
            )
        except ValueError as exc:
            return json_response(self, 400, {"error": str(exc)})
        except Exception as exc:
            audit_admin("reviewer.invite_failed", str(exc))
            return json_response(self, 500, {"error": f"email send failed: {exc}"})
        audit_admin("reviewer.invite", f"{result['reviewer_code']} {result['email']}")
        return json_response(self, 200, {
            "ok": True,
            "reviewer_code": result["reviewer_code"],
            "email": result["email"],
            "sent_at": result["sent_at"],
            "invite_url": result["invite_url"],
        })

    def admin_disable_reviewer(self, payload: dict) -> None:
        code = str(payload.get("reviewer_code", "")).strip()
        disabled = bool(payload.get("disabled", True))
        if not code:
            return json_response(self, 400, {"error": "reviewer_code required"})
        ts = now_iso() if disabled else ""
        with db_connect() as db:
            db.execute(
                """
                INSERT INTO reviewers (reviewer_code, created_at, disabled_at)
                VALUES (?, ?, ?)
                ON CONFLICT(reviewer_code)
                DO UPDATE SET disabled_at = excluded.disabled_at
                """,
                (code, now_iso(), ts),
            )
            db.commit()
        audit_admin("reviewer.disable" if disabled else "reviewer.enable", code)
        return json_response(self, 200, {"ok": True, "reviewer_code": code, "disabled_at": ts})

    def admin_remove_reviewer(self, payload: dict) -> None:
        code = str(payload.get("reviewer_code", "")).strip()
        if not code:
            return json_response(self, 400, {"error": "reviewer_code required"})
        ts = now_iso()
        with db_connect() as db:
            row = db.execute(
                "SELECT disabled_at FROM reviewers WHERE reviewer_code = ?",
                (code,),
            ).fetchone()
            if not row:
                return json_response(self, 404, {"error": "unknown reviewer_code"})
            if not row[0]:
                return json_response(self, 400, {"error": "reviewer_code must be disabled before removal"})
            db.execute("DELETE FROM reviewers WHERE reviewer_code = ?", (code,))
            db.execute(
                """
                INSERT INTO removed_reviewers (reviewer_code, removed_at)
                VALUES (?, ?)
                ON CONFLICT(reviewer_code)
                DO UPDATE SET removed_at = excluded.removed_at
                """,
                (code, ts),
            )
            db.commit()
        audit_admin("reviewer.remove", code)
        return json_response(self, 200, {"ok": True, "reviewer_code": code, "removed_at": ts})

    def save_response(self, payload: dict) -> None:
        data = load_data()
        reviewer = reviewer_from_payload(payload)
        prop_id = str(payload.get("proposition_id", "")).strip()
        scores = payload.get("scores", [])
        preferences = payload.get("preferences", [])
        overall_note = str(payload.get("overall_note", ""))
        if not reviewer:
            return json_response(self, 400, {"error": "reviewer link required"})
        if not reviewer_exists(reviewer):
            return json_response(self, 403, {"error": "unknown or disabled reviewer link"})
        if not find_prop(data, prop_id):
            return json_response(self, 400, {"error": "unknown proposition_id"})
        if not prop_reviewable(data, reviewer, prop_id):
            return json_response(self, 403, {"error": "this proposition is available for browsing but is not assigned for review"})
        metric_ids = {m["id"] for m in data["rubric"]["metrics"]}
        preference_question_ids = {q["id"] for q in data.get("preference_questions", {}).get("questions", [])}
        method_ids = set(find_prop(data, prop_id)["methods"].keys())
        ts = now_iso()
        with db_connect() as db:
            for item in scores:
                method_id = item.get("method_id")
                metric_id = item.get("metric_id")
                score = item.get("score")
                note = str(item.get("note", ""))
                if method_id not in method_ids or metric_id not in metric_ids or not isinstance(score, int) or not (0 <= score <= 5):
                    return json_response(self, 400, {"error": f"invalid score item: {item}"})
                db.execute(
                    """
                    INSERT INTO responses (reviewer_code, proposition_id, method_id, metric_id, score, note, updated_at)
                    VALUES (?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(reviewer_code, proposition_id, method_id, metric_id)
                    DO UPDATE SET score = excluded.score, note = excluded.note, updated_at = excluded.updated_at
                    """,
                    (reviewer, prop_id, method_id, metric_id, score, note, ts),
                )
            for item in preferences:
                question_id = str(item.get("question_id", "")).strip()
                choice = item.get("choice")
                if question_id not in preference_question_ids or not isinstance(choice, int) or not (-3 <= choice <= 3):
                    return json_response(self, 400, {"error": f"invalid preference item: {item}"})
                choice_basis = str(item.get("choice_basis", "ui_slot")).strip()
                if choice_basis in {"method", "canonical_method", "canonical_method_v1"}:
                    negative_method_id = str(item.get("negative_method_id", "leaneuclid")).strip()
                    positive_method_id = str(item.get("positive_method_id", "new_method")).strip()
                    if negative_method_id != "leaneuclid" or positive_method_id != "new_method":
                        return json_response(self, 400, {"error": f"invalid preference method basis: {item}"})
                    stored_choice = choice
                elif choice_basis in {"ui_slot", "slot", ""}:
                    stored_choice = canonical_preference_choice(prop_id, choice)
                else:
                    return json_response(self, 400, {"error": f"invalid preference choice basis: {item}"})
                db.execute(
                    """
                    INSERT INTO preference_responses (reviewer_code, proposition_id, question_id, choice, updated_at)
                    VALUES (?, ?, ?, ?, ?)
                    ON CONFLICT(reviewer_code, proposition_id, question_id)
                    DO UPDATE SET choice = excluded.choice, updated_at = excluded.updated_at
                    """,
                    (reviewer, prop_id, question_id, stored_choice, ts),
                )
            db.execute(
                """
                INSERT INTO overall_notes (reviewer_code, proposition_id, note, updated_at)
                VALUES (?, ?, ?, ?)
                ON CONFLICT(reviewer_code, proposition_id)
                DO UPDATE SET note = excluded.note, updated_at = excluded.updated_at
                """,
                (reviewer, prop_id, overall_note, ts),
            )
            db.commit()
        return json_response(self, 200, {"ok": True, "updated_at": ts})

    def save_tutorial(self, payload: dict) -> None:
        reviewer = reviewer_from_payload(payload)
        version = str(payload.get("tutorial_version", TUTORIAL_VERSION)).strip() or TUTORIAL_VERSION
        if not reviewer:
            return json_response(self, 400, {"error": "reviewer link required"})
        if not reviewer_exists(reviewer):
            return json_response(self, 403, {"error": "unknown or disabled reviewer link"})
        if version != TUTORIAL_VERSION:
            return json_response(self, 400, {"error": "unknown tutorial_version"})
        ts = now_iso()
        with db_connect() as db:
            db.execute(
                """
                INSERT INTO reviewer_tutorials (reviewer_code, tutorial_version, completed_at, updated_at)
                VALUES (?, ?, ?, ?)
                ON CONFLICT(reviewer_code, tutorial_version)
                DO UPDATE SET updated_at = excluded.updated_at
                """,
                (reviewer, version, ts, ts),
            )
            db.commit()
        return json_response(self, 200, {
            "ok": True,
            "reviewer_code": reviewer,
            "tutorial_version": version,
            "completed": True,
            "completed_at": ts,
            "updated_at": ts,
        })

    def lean_state(self, payload: dict) -> None:
        data = load_data()
        client_id = lean_client_id(payload.get("client_id"))
        prop_id = str(payload.get("proposition_id", ""))
        method_id = str(payload.get("method_id", ""))
        file_path = str(payload.get("file_path", ""))
        line = int(payload.get("line", 1))
        column = int(payload.get("column", 0))
        allowed = allowed_file(data, prop_id, method_id, file_path)
        if not allowed:
            return json_response(self, 400, {"error": "file is not an allowed survey or dependency source"})
        root, full = allowed
        ensure_current_prop(prop_id, client_id)
        state_request_id = next_state_request(prop_id, client_id)
        return json_response(self, 200, run_lean_state(root, full, line, column, prop_id, state_request_id, client_id))

    def lean_hover(self, payload: dict) -> None:
        data = load_data()
        client_id = lean_client_id(payload.get("client_id"))
        prop_id = str(payload.get("proposition_id", ""))
        method_id = str(payload.get("method_id", ""))
        file_path = str(payload.get("file_path", ""))
        line = int(payload.get("line", 1))
        column = int(payload.get("column", 0))
        allowed = allowed_file(data, prop_id, method_id, file_path)
        if not allowed:
            return json_response(self, 400, {"error": "file is not an allowed survey or dependency source"})
        root, full = allowed
        file_hash = hashlib.sha256(full.read_bytes()).hexdigest()
        session = get_lean_session(root, full, file_hash, prop_id, client_id=client_id)
        touch_interactive_prop_cache(prop_id, client_id)
        try:
            result = session.hover(line, column)
        except TimeoutError:
            discard_lean_session(root, full, file_hash, prop_id)
            raise
        return json_response(self, 200, result)

    def lean_definition(self, payload: dict) -> None:
        data = load_data()
        client_id = lean_client_id(payload.get("client_id"))
        prop_id = str(payload.get("proposition_id", ""))
        method_id = str(payload.get("method_id", ""))
        file_path = str(payload.get("file_path", ""))
        line = int(payload.get("line", 1))
        column = int(payload.get("column", 0))
        allowed = allowed_file(data, prop_id, method_id, file_path)
        if not allowed:
            return json_response(self, 400, {"error": "file is not an allowed survey or dependency source"})
        root, full = allowed
        file_hash = hashlib.sha256(full.read_bytes()).hexdigest()
        session = get_lean_session(root, full, file_hash, prop_id, client_id=client_id)
        touch_interactive_prop_cache(prop_id, client_id)
        method = find_prop(data, prop_id)["methods"][method_id]
        method_root = resolve_project_root(method["root"])
        manifest_files = {str((method_root / f["path"]).resolve()): f["path"] for f in method.get("files", [])}
        enriched = []
        try:
            locations = session.definition(line, column)
        except TimeoutError:
            discard_lean_session(root, full, file_hash, prop_id)
            raise
        for loc in locations:
            path = Path(loc["path"]).resolve()
            rng = loc.get("range") or {}
            rel = manifest_files.get(str(path))
            item = {
                **loc,
                "filePath": rel or str(path),
                "line": (rng.get("start") or {}).get("line", 1),
                "column": (rng.get("start") or {}).get("column", 0),
                "inManifest": bool(rel),
            }
            if not rel and path.exists() and path.suffix == ".lean" and any(is_relative_to(path, r) for r in safe_source_roots(root)):
                item["source"] = source_payload(path, str(path))
            enriched.append(item)
        return json_response(self, 200, {"locations": enriched})

    def lean_info_hover(self, payload: dict) -> None:
        data = load_data()
        client_id = lean_client_id(payload.get("client_id"))
        prop_id = str(payload.get("proposition_id", ""))
        method_id = str(payload.get("method_id", ""))
        file_path = str(payload.get("file_path", ""))
        line = int(payload.get("line", 1))
        column = int(payload.get("column", 0))
        session_id = payload.get("rpc_session_id", "")
        info_ref = payload.get("info_ref")
        allowed = allowed_file(data, prop_id, method_id, file_path)
        if not allowed:
            return json_response(self, 400, {"error": "file is not an allowed survey or dependency source"})
        if not session_id:
            return json_response(self, 400, {"error": "missing Lean RPC session id"})
        root, full = allowed
        file_hash = hashlib.sha256(full.read_bytes()).hexdigest()
        session = get_lean_session(root, full, file_hash, prop_id, client_id=client_id)
        touch_interactive_prop_cache(prop_id, client_id)
        return json_response(self, 200, session.info_hover(session_id, line, column, info_ref))

    def lean_trace_children(self, payload: dict) -> None:
        data = load_data()
        client_id = lean_client_id(payload.get("client_id"))
        prop_id = str(payload.get("proposition_id", ""))
        method_id = str(payload.get("method_id", ""))
        file_path = str(payload.get("file_path", ""))
        line = int(payload.get("line", 1))
        column = int(payload.get("column", 0))
        session_id = payload.get("rpc_session_id", "")
        trace_ref = payload.get("trace_ref")
        if not session_id or not isinstance(trace_ref, dict):
            return json_response(self, 400, {"error": "rpc_session_id and trace_ref are required"})
        allowed = allowed_file(data, prop_id, method_id, file_path)
        if not allowed:
            return json_response(self, 400, {"error": "file is not an allowed survey or dependency source"})
        root, full = allowed
        file_hash = hashlib.sha256(full.read_bytes()).hexdigest()
        session = get_lean_session(root, full, file_hash, prop_id, client_id=client_id)
        touch_interactive_prop_cache(prop_id, client_id)
        return json_response(self, 200, session.trace_children(session_id, line, column, trace_ref))

    def lean_warm(self, payload: dict) -> None:
        if os.environ.get("LEAN_SURVEY_DISABLE_RPC", "").lower() in ("1", "true", "yes"):
            return json_response(self, 200, {"ok": False, "mode": "disabled"})
        prop_id = str(payload.get("proposition_id", ""))
        client_id = lean_client_id(payload.get("client_id"))
        reviewer_code = reviewer_from_payload(payload)
        if not reviewer_code:
            return json_response(self, 400, {"error": "reviewer link required"})
        if not reviewer_exists(reviewer_code):
            return json_response(self, 403, {"error": "unknown or disabled reviewer link"})
        files = [item for item in payload.get("files", []) if isinstance(item, dict)]
        return json_response(self, 200, enqueue_warm_request(prop_id, files, client_id, reviewer_code))

    def lean_warm_status(self, payload: dict) -> None:
        request_id = str(payload.get("request_id", ""))
        status = warm_request_snapshot(request_id)
        if not status:
            return json_response(self, 404, {"error": "unknown warm-up request"})
        return json_response(self, 200, status)

    def serve_static(self, path: str) -> None:
        if path in ("", "/"):
            rel = "index.html"
        else:
            rel = unquote(path.lstrip("/"))
        full = (WEB_DIR / rel).resolve()
        try:
            full.relative_to(WEB_DIR.resolve())
        except ValueError:
            return text_response(self, 403, "forbidden")
        if not full.exists() or full.is_dir():
            full = WEB_DIR / "index.html"
        content_type = {
            ".html": "text/html; charset=utf-8",
            ".css": "text/css; charset=utf-8",
            ".js": "application/javascript; charset=utf-8",
            ".json": "application/json; charset=utf-8",
            ".svg": "image/svg+xml",
        }.get(full.suffix, "application/octet-stream")
        body = full.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def serve_admin_static(self, path: str) -> None:
        admin_dir = WEB_DIR / "admin"
        if path in ("/admin", "/admin/"):
            rel = "index.html"
        else:
            rel = unquote(path.removeprefix("/admin/"))
        full = (admin_dir / rel).resolve()
        try:
            full.relative_to(admin_dir.resolve())
        except ValueError:
            return text_response(self, 403, "forbidden")
        if not full.exists() or full.is_dir():
            full = admin_dir / "index.html"
        content_type = {
            ".html": "text/html; charset=utf-8",
            ".css": "text/css; charset=utf-8",
            ".js": "application/javascript; charset=utf-8",
            ".json": "application/json; charset=utf-8",
            ".svg": "image/svg+xml",
        }.get(full.suffix, "application/octet-stream")
        body = full.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    init_db()
    data = load_data()
    start_warm_workers()
    enqueue_startup_pinned_warmups(data)
    httpd = ThreadingHTTPServer((args.host, args.port), SurveyHandler)
    print(f"survey server: http://{args.host}:{args.port}")
    print(f"database: {DB_PATH}")
    httpd.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
