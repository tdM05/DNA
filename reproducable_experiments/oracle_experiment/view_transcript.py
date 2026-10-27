#!/usr/bin/env python3
# =============================================================================
# view_transcript.py -- READ-ONLY transcript viewer for ablation-study runs
# =============================================================================
#
# This is a *viewing only* tool. It NEVER launches `claude`, never resumes a
# session, and never spends budget. It just parses a run's transcript.jsonl and
# pretty-prints it into a scrollable pager (`less -R`). There is no way to
# accidentally continue an agent from here.
#
# USAGE:
#   python3 view_transcript.py
#       -> interactive PICKER: lists every run under out/ (mode / prop / status)
#          and lets you choose one by number.
#
#   python3 view_transcript.py <n>
#       -> open run number <n> from the picker list directly.
#
#   python3 view_transcript.py <path>
#       -> <path> may be a session dir, a transcript.jsonl file, or any dir that
#          contains one.
#
#   python3 view_transcript.py <session-id>
#       -> find the run whose transcript is <session-id>.jsonl anywhere under out/.
#
# The wrapper `view_transcript.sh` just calls this script.
# =============================================================================
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "out")
PROJECTS = os.path.expanduser("~/.claude/projects")  # where live session transcripts live

# ---- ANSI helpers (only used when writing to the pager) --------------------
C = {
    "reset": "\033[0m", "dim": "\033[2m", "bold": "\033[1m",
    "user": "\033[1;36m",      # cyan
    "assistant": "\033[1;32m", # green
    "thinking": "\033[2;37m",  # dim grey
    "tool": "\033[1;33m",      # yellow
    "result": "\033[0;35m",    # magenta
    "err": "\033[1;31m",       # red
    "hdr": "\033[1;44;97m",    # blue banner
    "sep": "\033[2;34m",
}


def col(key, s):
    return f"{C[key]}{s}{C['reset']}"


# ---- timestamps ------------------------------------------------------------
def parse_ts(s):
    """Parse a transcript ISO-8601 timestamp into a local-tz datetime."""
    if not s:
        return None
    try:
        dt = datetime.fromisoformat(str(s).replace("Z", "+00:00"))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone()
    except (ValueError, TypeError):
        return None


def fmt_delta(d):
    """A compact '+Δ' string for `d` seconds since the previous item."""
    if d < 0:
        d = 0
    if d < 60:
        return f"+{d:.1f}s"
    m, s = divmod(int(round(d)), 60)
    if m < 60:
        return f"+{m}m{s:02d}s"
    h, m = divmod(m, 60)
    return f"+{h}h{m:02d}m"


# width of the "HH:MM:SS   +Δ " prefix, so body lines can align under it
TAGW = 20


def time_tag(ts, state):
    """A dim 'HH:MM:SS   +Δsince-last ' prefix. Updates state['last'].
    Returns a blank, same-width pad when no timestamp is available."""
    if ts is None:
        return col("dim", " " * TAGW)
    last = state.get("last")
    delta = fmt_delta((ts - last).total_seconds()) if last is not None else ""
    state["last"] = ts
    tag = f"{ts.strftime('%H:%M:%S')} {delta:>9} "
    return col("dim", tag.ljust(TAGW))


# ---- run discovery ---------------------------------------------------------
def find_runs():
    """Every session dir under out/ that has a transcript.jsonl."""
    runs = []
    if not os.path.isdir(OUT):
        return runs
    for dirpath, dirnames, filenames in os.walk(OUT):
        # a "run" is a session dir with EITHER a local transcript copy OR a
        # result.txt (a still-RUNNING run has only the latter — its live
        # transcript is still in ~/.claude/projects).
        if "transcript.jsonl" in filenames or "result.txt" in filenames:
            runs.append(dirpath)
            dirnames[:] = []  # don't descend past a session dir
    runs.sort()
    return runs


def read_result(session_dir):
    """Parse result.txt (key: value lines) if present."""
    meta = {}
    rf = os.path.join(session_dir, "result.txt")
    if os.path.isfile(rf):
        for line in open(rf, encoding="utf-8", errors="replace"):
            if ":" in line:
                k, _, v = line.partition(":")
                meta[k.strip()] = v.strip()
    return meta


def transcript_path(session_dir):
    """The transcript for a run: prefer the local copy, else the live
    ~/.claude/projects/... file recorded in result.txt (running runs)."""
    local = os.path.join(session_dir, "transcript.jsonl")
    if os.path.isfile(local):
        return local
    t = read_result(session_dir).get("transcript")
    if t and os.path.isfile(t):
        return t
    return None


def run_label(session_dir):
    rel = os.path.relpath(session_dir, OUT)
    parts = rel.split(os.sep)
    mode = parts[0] if parts else "?"
    prop = parts[1] if len(parts) > 1 else "?"
    stamp = parts[2] if len(parts) > 2 else ""
    meta = read_result(session_dir)
    status = meta.get("result") or meta.get("stop_reason") or "running/incomplete"
    return mode, prop, stamp, status


def print_picker(runs):
    print(col("hdr", " ablation-study transcripts (READ-ONLY viewer) "))
    print()
    cur_mode = cur_prop = None
    for i, r in enumerate(runs):
        mode, prop, stamp, status = run_label(r)
        if mode != cur_mode:
            print(col("bold", f"\n[{mode}]"))
            cur_mode = mode
            cur_prop = None
        if prop != cur_prop:
            print(col("bold", f"  {prop}"))
            cur_prop = prop
        scol = "assistant" if status.upper().startswith("SUCCESS") else (
            "err" if "FAIL" in status.upper() else "tool")
        live = "" if os.path.isfile(os.path.join(r, "transcript.jsonl")) else col("tool", " ‹live›")
        print(f"    {i:>3})  {stamp:<28}  {col(scol, status)}{live}")
    print()
    print(col("dim", "Pick a number to view (q to quit): "), end="", flush=True)


# ---- target resolution -----------------------------------------------------
def resolve(arg, runs):
    """Turn a CLI arg into a transcript.jsonl path."""
    # 1) index into the picker list
    if re.fullmatch(r"\d+", arg):
        idx = int(arg)
        if 0 <= idx < len(runs):
            return transcript_path(runs[idx])
        # fall through: maybe it's a numeric-looking path? unlikely.
    # 2) explicit file
    if os.path.isfile(arg):
        return arg
    # 3) a directory containing a transcript
    if os.path.isdir(arg):
        tp = transcript_path(arg)
        if tp:
            return tp
        # search inside it
        for dp, _, fn in os.walk(arg):
            if "transcript.jsonl" in fn:
                return os.path.join(dp, "transcript.jsonl")
    # 4) a session-id -> its run under out/ (uses the live projects file if the
    #    run is still running and hasn't been copied locally yet), ...
    for r in runs:
        if read_result(r).get("session_id") == arg:
            tp = transcript_path(r)
            if tp:
                return tp
    # ... or the raw <sid>.jsonl in ~/.claude/projects (same place `claude
    #    --resume` reads from), or anywhere under out/.
    for root in (PROJECTS, OUT):
        if not os.path.isdir(root):
            continue
        for dp, _, fn in os.walk(root):
            if f"{arg}.jsonl" in fn:
                return os.path.join(dp, f"{arg}.jsonl")
    return None


# ---- rendering (Claude-Code-like) ------------------------------------------
PREVIEW_LINES = 12   # how many lines of a tool result to show before collapsing
INDENT = "     "     # body indent under a "●" bullet


def _text_of(content):
    """Flatten a message/result content field to a plain string."""
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        out = []
        for c in content:
            if isinstance(c, dict):
                out.append(c.get("text", "") if c.get("type") == "text" else c.get("text", ""))
            else:
                out.append(str(c))
        return "\n".join(x for x in out if x)
    return "" if content is None else str(content)


def _preview(text, marker, cont, colour, n=PREVIEW_LINES):
    """First n lines of `text`: line 0 gets `marker`, rest get `cont` indent,
    then a dim '+N lines' tail. Returns a list of coloured lines."""
    text = text.rstrip("\n")
    raw = text.split("\n") if text.strip() else []
    if not raw:
        return [col(colour, marker + "(empty)")]
    shown = raw[:n]
    body = [col(colour, marker + shown[0])]
    body += [col(colour, cont + ln) for ln in shown[1:]]
    extra = len(raw) - len(shown)
    if extra > 0:
        body.append(col("dim", cont + f"… +{extra} lines"))
    return body


def tool_summary(item):
    """A compact 'Tool(arg)' header line, mimicking Claude Code."""
    name = item.get("name", "?")
    inp = item.get("input", {}) or {}

    def one(s, n=140):
        s = " ".join(str(s).split())
        return s if len(s) <= n else s[: n - 1] + "…"

    if name == "Bash":
        arg = one(inp.get("command", ""))
    elif name in ("Read", "Write", "NotebookEdit"):
        arg = inp.get("file_path") or inp.get("notebook_path") or ""
    elif name in ("Edit", "MultiEdit"):
        arg = inp.get("file_path", "")
    elif name in ("Grep", "Glob"):
        arg = one(inp.get("pattern", ""))
        if inp.get("path"):
            arg += f"  ({inp['path']})"
    elif name == "Task" or name == "Agent":
        arg = one(inp.get("description") or inp.get("prompt", ""))
    elif name == "TodoWrite":
        arg = ""
    else:
        arg = one(json.dumps(inp, ensure_ascii=False), 140)
    return col("tool", f"● {name}") + (col("dim", f"({arg})") if arg else "")


def render_message(o, results, out, state):
    """Render one user/assistant transcript entry into `out` (list of lines).
    Every item is prefixed with a time tag (and the delta since the previous
    item), so it's easy to see how much time passed between things."""
    typ = o["type"]
    ts = parse_ts(o.get("timestamp"))
    content = o.get("message", {}).get("content", [])
    if not isinstance(content, list):
        content = [{"type": "text", "text": _text_of(content)}]

    for it in content:
        if isinstance(it, str):
            it = {"type": "text", "text": it}
        t = it.get("type")

        if t == "text":
            txt = it.get("text", "").strip()
            if not txt:
                continue
            if typ == "user":
                # a real user/human message (not a tool result)
                out.append("")
                out.append(time_tag(ts, state) + col("user", "❯ user"))
                out.extend(col("user", INDENT + ln) for ln in txt.split("\n"))
            else:
                out.append("")
                tl = txt.split("\n")
                out.append(time_tag(ts, state) + col("assistant", "● ") + tl[0])
                out.extend("  " + ln for ln in tl[1:])

        elif t == "thinking":
            think = it.get("thinking", "").strip()
            if not think:
                continue
            out.append("")
            out.append(time_tag(ts, state) + col("thinking", "✻ thinking"))
            out.extend(_preview(think, INDENT, INDENT, "thinking", n=6))

        elif t == "tool_use":
            out.append("")
            out.append(time_tag(ts, state) + tool_summary(it))
            res = results.get(it.get("id"))
            if res is not None:
                rtext = _text_of(res.get("content", ""))
                colour = "err" if res.get("is_error") else "dim"
                out.extend(_preview(rtext, "  ⎿  ", "     ", colour))

        elif t == "image":
            out.append(time_tag(ts, state) + col("dim", "● [image]"))
        # tool_result blocks in user turns are attached to their tool_use above,
        # so we skip them here.


def render(path):
    entries = []
    results = {}
    for raw in open(path, encoding="utf-8", errors="replace"):
        raw = raw.strip()
        if not raw:
            continue
        try:
            o = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if o.get("type") not in ("user", "assistant"):
            continue
        entries.append(o)
        # index tool results (they live in user turns) by tool_use_id
        content = o.get("message", {}).get("content", [])
        if isinstance(content, list):
            for c in content:
                if isinstance(c, dict) and c.get("type") == "tool_result":
                    results[c.get("tool_use_id")] = c

    lines = []
    state = {"last": None}  # tracks the previous item's timestamp for deltas
    for o in entries:
        render_message(o, results, lines, state)

    header = [
        col("hdr", " READ-ONLY TRANSCRIPT VIEW — no agent is running, nothing is being spent "),
        col("dim", f" file: {path}"),
        col("dim", " each item is tagged  HH:MM:SS  +Δsince-previous-item (local time)"),
        col("dim", " opens at END · scroll: mouse-wheel / ↑↓ / PgUp-PgDn · g=top G=end · /=search · q=quit"),
    ]
    return "\n".join(header + lines) + "\n"


def page(text):
    if not sys.stdout.isatty():
        sys.stdout.write(text)
        return
    # -R keep colors · --mouse wheel-scroll · +G start at the END of the transcript
    less = ["less", "-R", "--mouse", "--wheel-lines=3", "+G"]
    try:
        p = subprocess.Popen(less, stdin=subprocess.PIPE)
        p.communicate(text.encode("utf-8", errors="replace"))
    except (BrokenPipeError, KeyboardInterrupt):
        pass
    except FileNotFoundError:
        sys.stdout.write(text)
    finally:
        # `less --mouse` can leave the terminal with mouse-tracking and
        # application-cursor-key mode still ON, which then leaks bytes like
        # "OA" into the shell after quitting. Explicitly turn them back off.
        if sys.stdout.isatty():
            #      mouse: 1000/1002/1003/1006/1015 off   · app-cursor-keys off · normal keypad
            sys.stdout.write("\033[?1000l\033[?1002l\033[?1003l\033[?1006l\033[?1015l\033[?1l\033>")
            sys.stdout.flush()


def main():
    runs = find_runs()
    arg = sys.argv[1] if len(sys.argv) > 1 else None

    if arg is None:
        if not runs:
            print(f"no transcripts found under {OUT}")
            return 1
        print_picker(runs)
        try:
            choice = sys.stdin.readline().strip()
        except (EOFError, KeyboardInterrupt):
            print()
            return 0
        if choice.lower() in ("", "q", "quit", "exit"):
            return 0
        arg = choice

    path = resolve(arg, runs)
    if not path:
        print(f"could not resolve a transcript from: {arg!r}")
        print("(pass a picker number, a session dir, a transcript.jsonl, or a session-id)")
        return 1
    page(render(path))
    return 0


if __name__ == "__main__":
    sys.exit(main())
