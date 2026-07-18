#!/usr/bin/env python3
"""transcript_tui.py — navigate the fill-comparison Claude Code .jsonl transcripts.

Launch with NO arguments to get an in-TUI PICKER: choose the method (naive/ablated vs
ordered_decomp) and the prop, then browse. Press 'o' any time to return to the picker and
switch to a different session. (You can still pass a .jsonl path directly to jump straight in.)

Two things this tool surfaces per transcript:

  1. STOPS — every time the agent ENDED ITS TURN (stop_reason == "end_turn") to address the
     human, classified by what kind of stop it was:
        gave_up  — "I cannot synthesise the missing step… I won't keep looping" (red)
        asked    — "Would you like me to continue … or pause here?"           (yellow)
        done     — hands back: "ready for review", "grader PASS", "yours to run" (green)
        wait     — "I'll wait for the background job / monitor" (a harness pause, NOT a real
                   stop; hidden by default, toggle with 'w')                    (dim)
        other    — substantive but uncategorised                               (cyan)
     For each stop we also show what made it CONTINUE — a `goal` (Stop-hook re-prompt), a
     `human` message, or `ended` (the session actually stopped there) — plus the agent's text
     as it stopped, the goal condition, and how it resumed.

  2. TOOL WALL TIME — each tool_use matched to its tool_result by id; duration = result.ts - use.ts.

Usage:
    python3 transcript_tui.py                    # PICKER: choose method + prop
    python3 transcript_tui.py <transcript.jsonl> # jump straight into one session
    python3 transcript_tui.py <transcript.jsonl> --dump   # plain-text report, no curses

TUI keys:
    PICKER:  j/k move   ENTER open   q quit
    VIEW:    TAB / 1 / 2   STOPS <-> TOOLS
             j/k or arrows move   PgDn/PgUp page   g/G top/bottom
             n / N        jump to next / prev GIVE-UP
             w            (STOPS) toggle showing 'wait' pauses
             s            (TOOLS) toggle sort chronological <-> slowest-first
             ENTER        open scrollable detail    o  back to picker    q quit
"""
import sys, os, json, re, datetime
from pathlib import Path


# ------------------------------------------------------------ stop classification
WAIT = re.compile(r"\b(wait|waiting|monitor event|notif|background job|stop polling|pause polling|"
                  r"resume (?:when|automatically)|re-invoke|be notified|completion (?:event|notification))\b", re.I)
GAVE_UP = re.compile(r"(cannot |can'?t (?:synth|prove|derive|close|do|locate|find|complete)|won'?t keep|"
                     r"unable to|not able to|fail-datum|ablation (?:data|fail)|the (?:exact )?blocker|"
                     r"reach limit|unprovable|give up|recommend recording|missing (?:step|construction))", re.I)
ASK = re.compile(r"(would you like|want me to|shall i|should i|or pause|or \(?[bc]\)?[\)\s]|choose|"
                 r"option \d|let me know|you (?:choose|decide)|or something else|prefer)", re.I)
DONE = re.compile(r"(ready for (?:your )?review|nothing further|yours to run|human'?s to run|grader pass|"
                  r"\bpass\.|compiles cleanly|ready to act|all set|end to end.*(?:faithful|review))", re.I)

CAT_ORDER = ("gave_up", "asked", "done", "other", "wait")


def classify(t):
    s = (t or "").strip()
    if not s:
        return None
    if GAVE_UP.search(s):
        return "gave_up"
    if ASK.search(s) and "?" in s:
        return "asked"
    if DONE.search(s):
        return "done"
    if WAIT.search(s):
        return "wait"
    return "other"


def parse_ts(o):
    t = o.get("timestamp")
    if not t:
        return None
    try:
        return datetime.datetime.fromisoformat(t.replace("Z", "+00:00"))
    except ValueError:
        return None


def assistant_text(o):
    msg = o.get("message") or {}
    cont = msg.get("content")
    if not isinstance(cont, list):
        return ""
    out = [b.get("text", "") for b in cont if isinstance(b, dict) and b.get("type") == "text"]
    return "\n".join(t for t in out if t).strip()


def user_prompt(o):
    if o.get("type") != "user":
        return None
    c = (o.get("message") or {}).get("content")
    return c if isinstance(c, str) else None


def trigger_of(prompt):
    if prompt is None:
        return "ended"
    if "Stop hook" in prompt or "stop hook" in prompt:
        return "goal"
    if prompt.lstrip().startswith(("<task-notification", "<local-command", "<command-name")):
        return "system"
    return "human"


def tool_input_summary(name, inp):
    if not isinstance(inp, dict):
        return ""
    if name == "Bash":
        cmd = (inp.get("command") or "").strip().splitlines()
        first = cmd[0] if cmd else ""
        desc = inp.get("description") or ""
        return (desc + " :: " + first).strip(" :") if desc else first
    if name in ("Write", "Edit", "Read", "NotebookEdit"):
        return inp.get("file_path") or inp.get("notebook_path") or ""
    if name in ("TaskCreate", "TaskUpdate"):
        return str(inp.get("description") or inp.get("prompt") or inp.get("status") or "")[:120]
    s = json.dumps(inp, ensure_ascii=False)
    return s[:160]


def load(path):
    with open(path, encoding="utf-8") as f:
        lines = [json.loads(l) for l in f if l.strip()]

    uses, results = {}, {}
    for idx, o in enumerate(lines):
        cont = (o.get("message") or {}).get("content")
        if not isinstance(cont, list):
            continue
        for b in cont:
            if not isinstance(b, dict):
                continue
            if b.get("type") == "tool_use":
                uses[b["id"]] = dict(name=b.get("name", "?"), t0=parse_ts(o), input=b.get("input"), idx=idx)
            elif b.get("type") == "tool_result":
                results[b.get("tool_use_id")] = parse_ts(o)

    t0_all = min((u["t0"] for u in uses.values() if u["t0"]), default=None)
    tools = []
    for tid, u in uses.items():
        t1 = results.get(tid)
        dur = (t1 - u["t0"]).total_seconds() if (u["t0"] and t1) else None
        offset = (u["t0"] - t0_all).total_seconds() if (u["t0"] and t0_all) else None
        tools.append(dict(idx=u["idx"], name=u["name"], dur=dur, offset=offset,
                          summary=tool_input_summary(u["name"], u["input"]),
                          full=json.dumps(u["input"], ensure_ascii=False, indent=2), t0=u["t0"]))
    tools.sort(key=lambda t: t["idx"])

    events, n = [], 0
    for i, o in enumerate(lines):
        if o.get("type") != "assistant":
            continue
        if (o.get("message") or {}).get("stop_reason") != "end_turn":
            continue
        txt = assistant_text(o)
        cat = classify(txt)
        if cat is None:
            continue
        trig, cont_prompt = "ended", ""
        for j in range(i + 1, len(lines)):
            p = user_prompt(lines[j])
            if p is None:
                continue
            tg = trigger_of(p)
            if tg == "system":
                continue
            trig, cont_prompt = tg, p
            break
        resume = ""
        for j in range(i + 1, len(lines)):
            if lines[j].get("type") == "assistant":
                rt = assistant_text(lines[j])
                if rt:
                    resume = rt
                    break
        n += 1
        events.append(dict(idx=i, n=n, ts=parse_ts(o), cat=cat, give_up=txt.strip(),
                           resume=resume, trigger=trig, cont_prompt=cont_prompt.strip(),
                           goal=cont_prompt.strip() if trig == "goal" else "",
                           forced=(trig != "ended")))
    return lines, tools, events, t0_all


def cat_counts(events):
    c = {k: 0 for k in CAT_ORDER}
    for e in events:
        c[e["cat"]] = c.get(e["cat"], 0) + 1
    c["genuine"] = c["gave_up"] + c["asked"] + c["done"]
    return c


def discover(base):
    """Find (method, prop) -> transcript under base/{naive_llm,my_method}/<prop>/*.jsonl."""
    base = Path(base)
    specs = [("naive (ablated)", "naive_llm"), ("ordered_decomp", "my_method")]
    entries = []
    for label, sub in specs:
        d = base / sub
        if not d.is_dir():
            continue
        for pdir in sorted(d.iterdir()):
            if not pdir.is_dir():
                continue
            js = sorted(pdir.glob("*.jsonl"))
            if js:
                entries.append(dict(method=label, sub=sub, prop=pdir.name, path=str(js[0])))

    def key(e):
        try:
            p = tuple(int(x) for x in e["prop"].split("."))
        except Exception:
            p = (9999,)
        return (p, e["sub"])
    entries.sort(key=key)
    return entries


# ---------------------------------------------------------------- plain dump
def fmt_dur(d):
    return "   n/a" if d is None else "%6.1fs" % d


def dump(path):
    lines, tools, events, t0 = load(path)
    c = cat_counts(events)
    print("=" * 78)
    print("TRANSCRIPT:", path)
    print("lines=%d  tool_calls=%d  stops=%d" % (len(lines), len(tools), len(events)))
    print("  genuine stops=%d  (gave_up=%d, asked=%d, done=%d)  | other=%d  wait=%d" % (
        c["genuine"], c["gave_up"], c["asked"], c["done"], c["other"], c["wait"]))
    total = sum(t["dur"] for t in tools if t["dur"])
    print("total tool wall time: %.1f s (%.1f min)" % (total, total / 60))
    print()
    print("### STOPS  (wait pauses excluded)")
    for e in events:
        if e["cat"] == "wait":
            continue
        print("-" * 78)
        print("[#%d] line %d  %s  %-8s  continued-by:%s%s" % (
            e["n"], e["idx"], e["ts"].strftime("%H:%M:%S") if e["ts"] else "?",
            e["cat"].upper(), e["trigger"], "" if e["forced"] else "  (TERMINAL)"))
        for ln in e["give_up"].splitlines()[:8]:
            print("    | " + ln)
        if e["goal"]:
            print("  goal that forced continue:")
            for ln in e["goal"].splitlines()[:3]:
                print("    * " + ln)
    print()
    print("### SLOWEST 15 TOOL CALLS")
    for t in sorted(tools, key=lambda x: -(x["dur"] or -1))[:15]:
        print("  %s  %-11s  %s" % (fmt_dur(t["dur"]), t["name"], t["summary"][:80]))
    from collections import Counter
    by, tt = Counter(), Counter()
    for t in tools:
        by[t["name"]] += 1
        tt[t["name"]] += t["dur"] or 0
    print()
    print("### TOOL TOTALS")
    for name, cnt in by.most_common():
        print("  %-11s count=%-4d total=%7.1fs" % (name, cnt, tt[name]))


# ---------------------------------------------------------------- curses TUI
CAT_COLOR = {"gave_up": 4, "asked": 2, "done": 3, "other": 1, "wait": 0}


def run_app(base, initial_path=None):
    import curses
    import textwrap
    entries = discover(base)

    data = {}                                   # path, lines, tools, events (current session)
    sel = [0, 0]
    top = [0, 0]
    state = dict(tab=0, sort_dur=False, show_waits=False)
    psel = [0]
    ptop = [0]
    mode = ["pick"]

    def load_path(p):
        lines, tools, events, _ = load(p)
        data.clear()
        data.update(path=p, lines=lines, tools=tools, events=events)
        sel[0] = sel[1] = top[0] = top[1] = 0
        state["tab"] = 0

    if initial_path:
        load_path(initial_path)
        mode[0] = "view"

    def vis_events():
        ev = data.get("events", [])
        return [e for e in ev if state["show_waits"] or e["cat"] != "wait"]

    def sorted_tools():
        tl = data.get("tools", [])
        if state["sort_dur"]:
            return sorted(tl, key=lambda x: -(x["dur"] if x["dur"] is not None else -1))
        return tl

    def detail_lines_event(e):
        L = [("h", "STOP #%d   [%s]   (line %d)" % (e["n"], e["cat"].upper(), e["idx"]))]
        L.append(("", "time: %s   continued by: %s%s" % (
            e["ts"].strftime("%Y-%m-%d %H:%M:%S") if e["ts"] else "?",
            e["trigger"], "" if e["forced"] else "   (TERMINAL — session stopped here)")))
        L.append(("", ""))
        L.append(("h", ">>> WHAT THE AGENT SAID AS IT STOPPED"))
        col = {"gave_up": "r", "asked": "y", "done": "g"}.get(e["cat"], "")
        for para in e["give_up"].splitlines():
            for ln in (textwrap.wrap(para, 92) or [""]):
                L.append((col, "  " + ln))
        if e["goal"]:
            L.append(("", ""))
            L.append(("h", ">>> GOAL / STOP-HOOK THAT FORCED IT TO CONTINUE"))
            for para in e["goal"].splitlines():
                for ln in (textwrap.wrap(para, 92) or [""]):
                    L.append(("y", "  " + ln))
        L.append(("", ""))
        L.append(("h", ">>> HOW IT RESUMED"))
        for para in (e["resume"] or "(no follow-up text — terminal stop)").splitlines():
            for ln in (textwrap.wrap(para, 92) or [""]):
                L.append(("g", "  " + ln))
        return L

    def detail_lines_tool(t):
        L = [("h", "TOOL CALL  %s   (line %d)" % (t["name"], t["idx"]))]
        L.append(("", "duration: %s    offset from start: %s" % (
            fmt_dur(t["dur"]), "%.1fs" % t["offset"] if t["offset"] is not None else "?")))
        L.append(("", "started: %s" % (t["t0"].strftime("%H:%M:%S") if t["t0"] else "?")))
        L.append(("", ""))
        L.append(("h", "INPUT"))
        for para in t["full"].splitlines():
            for ln in (textwrap.wrap(para, 92) or [""]):
                L.append(("", "  " + ln))
        return L

    def draw_picker(scr, h, w):
        scr.addstr(0, 0, (" TRANSCRIPT TUI — pick a session   [%s]" % os.path.basename(str(base)))[:w - 1],
                   curses.A_REVERSE)
        if not entries:
            scr.addstr(2, 0, "  no transcripts found under naive_llm/ or my_method/"[:w - 1])
            scr.addstr(h - 1, 0, " q quit"[:w - 1], curses.A_DIM)
            return
        scr.addstr(2, 0, "   #  method            prop"[:w - 1], curses.A_BOLD)
        listtop, rows = 4, h - 6
        cs = psel[0]
        if cs < ptop[0]:
            ptop[0] = cs
        if cs >= ptop[0] + rows:
            ptop[0] = cs - rows + 1
        for r in range(rows):
            i = ptop[0] + r
            if i >= len(entries):
                break
            e = entries[i]
            line = "  %2d  %-16s  %s" % (i + 1, e["method"], e["prop"])
            scr.addstr(listtop + r, 0, line[:w - 1], curses.A_REVERSE if i == psel[0] else curses.A_NORMAL)
        scr.addstr(h - 1, 0, " j/k move   ENTER open   q quit"[:w - 1], curses.A_DIM)

    def draw_list(scr, h, w):
        tab = state["tab"]
        events = data.get("events", [])
        tools = data.get("tools", [])
        c = cat_counts(events)
        title = " %s  —  %s" % (os.path.basename(data.get("path", "")), _label_for(data.get("path", "")))
        scr.addstr(0, 0, title[:w - 1], curses.A_REVERSE)
        total = sum(x["dur"] for x in tools if x["dur"])
        tabs = "[1] STOPS(gave_up %d/asked %d/done %d)   [2] TOOLS(%d)" % (
            c["gave_up"], c["asked"], c["done"], len(tools))
        meta = "tools wall %.0fs/%.1fmin" % (total, total / 60)
        scr.addstr(1, 0, tabs[:w - 1], curses.A_BOLD)
        scr.addstr(1, max(0, w - len(meta) - 1), meta[:w - 1])
        if tab == 0:
            hint = " j/k move  n/N give-up  w waits(%s)  ENTER detail  o pick  TAB tools  q quit" % (
                "on" if state["show_waits"] else "off")
        else:
            hint = " j/k move  s sort(%s)  n/N give-up  ENTER detail  o pick  TAB stops  q quit" % (
                "slowest" if state["sort_dur"] else "chrono")
        scr.addstr(2, 0, hint[:w - 1], curses.A_DIM)

        listtop, rows = 4, h - 4
        items = vis_events() if tab == 0 else sorted_tools()
        cursel = min(sel[tab], max(0, len(items) - 1))
        sel[tab] = cursel
        if cursel < top[tab]:
            top[tab] = cursel
        if cursel >= top[tab] + rows:
            top[tab] = cursel - rows + 1
        for r in range(rows):
            idx = top[tab] + r
            if idx >= len(items):
                break
            if tab == 0:
                e = items[idx]
                snip = (e["give_up"].splitlines() or [""])[0]
                line = "#%-3d %s %-8s %-7s %s" % (
                    e["n"], e["ts"].strftime("%H:%M:%S") if e["ts"] else "  ?  ",
                    e["cat"].upper(), e["trigger"], snip)
                pair = CAT_COLOR.get(e["cat"], 0)
                attr = curses.A_REVERSE if idx == cursel else (
                    curses.color_pair(pair) if pair else curses.A_DIM)
            else:
                t = items[idx]
                bar = "#" * min(20, int(t["dur"] / 6)) if t["dur"] is not None else ""
                line = "%s %-11s %-20s %s" % (fmt_dur(t["dur"]), t["name"], bar, t["summary"])
                attr = curses.A_REVERSE if idx == cursel else (
                    curses.color_pair(4) if (t["dur"] or 0) >= 60 else curses.A_NORMAL)
            scr.addstr(listtop + r, 0, line[:w - 1], attr)

    def _label_for(path):
        for e in entries:
            if e["path"] == path:
                return "%s / %s" % (e["method"], e["prop"])
        return ""

    def draw_detail(scr, h, w, dlines, off):
        cmap = {"h": curses.A_BOLD | curses.color_pair(1), "g": curses.color_pair(3),
                "y": curses.color_pair(2), "r": curses.color_pair(4)}
        for r in range(h):
            idx = off + r
            if idx >= len(dlines):
                break
            kind, txt = dlines[idx]
            scr.addstr(r, 0, txt[:w - 1], cmap.get(kind, curses.A_NORMAL))
        foot = " [j/k scroll  g/G ends  q/ESC back]  line %d-%d/%d" % (
            off + 1, min(off + h, len(dlines)), len(dlines))
        scr.addstr(h, 0, foot[:w - 1], curses.A_REVERSE)

    def detail_loop(scr, dl):
        off = 0
        while True:
            scr.erase()
            h, w = scr.getmaxyx()
            draw_detail(scr, h - 1, w, dl, off)
            scr.refresh()
            k = scr.getch()
            if k in (ord("q"), 27):
                return
            elif k in (ord("j"), curses.KEY_DOWN):
                off = min(max(0, len(dl) - 1), off + 1)
            elif k in (ord("k"), curses.KEY_UP):
                off = max(0, off - 1)
            elif k == curses.KEY_NPAGE:
                off = min(max(0, len(dl) - 1), off + (h - 2))
            elif k == curses.KEY_PPAGE:
                off = max(0, off - (h - 2))
            elif k == ord("g"):
                off = 0
            elif k == ord("G"):
                off = max(0, len(dl) - (h - 1))

    def main(scr):
        curses.curs_set(0)
        curses.start_color()
        curses.use_default_colors()
        for i, col in ((1, curses.COLOR_CYAN), (2, curses.COLOR_YELLOW),
                       (3, curses.COLOR_GREEN), (4, curses.COLOR_RED)):
            curses.init_pair(i, col, -1)
        while True:
            scr.erase()
            h, w = scr.getmaxyx()

            if mode[0] == "pick":
                draw_picker(scr, h, w)
                scr.refresh()
                c = scr.getch()
                if c == ord("q"):
                    return
                elif c in (ord("j"), curses.KEY_DOWN):
                    psel[0] = min(len(entries) - 1, psel[0] + 1)
                elif c in (ord("k"), curses.KEY_UP):
                    psel[0] = max(0, psel[0] - 1)
                elif c == curses.KEY_NPAGE:
                    psel[0] = min(len(entries) - 1, psel[0] + (h - 6))
                elif c == curses.KEY_PPAGE:
                    psel[0] = max(0, psel[0] - (h - 6))
                elif c in (curses.KEY_ENTER, 10, 13) and entries:
                    load_path(entries[psel[0]]["path"])
                    mode[0] = "view"
                continue

            draw_list(scr, h, w)
            scr.refresh()
            c = scr.getch()
            tab = state["tab"]
            items = vis_events() if tab == 0 else sorted_tools()
            n_items = len(items)
            if c == ord("q"):
                return
            elif c == ord("o"):
                mode[0] = "pick"
            elif c in (ord("\t"), ord("1"), ord("2")):
                state["tab"] = 1 - tab if c == ord("\t") else (0 if c == ord("1") else 1)
            elif c in (ord("j"), curses.KEY_DOWN):
                sel[tab] = min(n_items - 1, sel[tab] + 1)
            elif c in (ord("k"), curses.KEY_UP):
                sel[tab] = max(0, sel[tab] - 1)
            elif c == curses.KEY_NPAGE:
                sel[tab] = min(n_items - 1, sel[tab] + (h - 5))
            elif c == curses.KEY_PPAGE:
                sel[tab] = max(0, sel[tab] - (h - 5))
            elif c == ord("g"):
                sel[tab] = 0
            elif c == ord("G"):
                sel[tab] = n_items - 1
            elif c == ord("w") and tab == 0:
                state["show_waits"] = not state["show_waits"]
                sel[0] = top[0] = 0
            elif c == ord("s") and tab == 1:
                state["sort_dur"] = not state["sort_dur"]
                sel[1] = top[1] = 0
            elif c in (ord("n"), ord("N")):
                d = 1 if c == ord("n") else -1
                if tab == 0:
                    gi = [k for k, e in enumerate(items) if e["cat"] == "gave_up"]
                    later = [k for k in gi if (k > sel[0] if d > 0 else k < sel[0])]
                    if later:
                        sel[0] = (min if d > 0 else max)(later)
                else:
                    ev = [e["idx"] for e in vis_events() if e["cat"] == "gave_up"]
                    cur = items[sel[1]]["idx"] if items else 0
                    cand = [x for x in ev if (x > cur if d > 0 else x < cur)]
                    if cand:
                        nxt = (min if d > 0 else max)(cand)
                        sel[1] = min(range(len(items)), key=lambda k: abs(items[k]["idx"] - nxt))
            elif c in (curses.KEY_ENTER, 10, 13):
                if tab == 0 and items:
                    detail_loop(scr, detail_lines_event(items[sel[0]]))
                elif tab == 1 and items:
                    detail_loop(scr, detail_lines_tool(items[sel[1]]))

    curses.wrapper(main)


if __name__ == "__main__":
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    flags = [a for a in sys.argv[1:] if a.startswith("--")]
    base = Path(__file__).resolve().parent
    if "--dump" in flags:
        if not args:
            print(__doc__)
            sys.exit(2)
        if not os.path.exists(args[0]):
            print("no such file:", args[0])
            sys.exit(2)
        dump(args[0])
    else:
        initial = args[0] if (args and os.path.exists(args[0])) else None
        run_app(base, initial)
