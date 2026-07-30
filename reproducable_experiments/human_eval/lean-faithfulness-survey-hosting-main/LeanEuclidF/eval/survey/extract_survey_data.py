#!/usr/bin/env python3
"""Build the JSON data bundle used by the faithfulness survey.

The extractor is intentionally source-based and lightweight. It does not require
Lean to run. Re-run it whenever new proposition formalizations are added.
"""

from __future__ import annotations

import json
import os
import re
from pathlib import Path
from typing import Any


SURVEY_DIR = Path(__file__).resolve().parent
LEANEUCLID_PLUS = SURVEY_DIR.parents[1]
WORKSPACE_ROOT = LEANEUCLID_PLUS.parents[1]


def env_path(name: str, default: Path, base: Path) -> Path:
    raw = os.environ.get(name)
    path = Path(raw) if raw else default
    return path if path.is_absolute() else (base / path).resolve()


LEANEUCLID_ROOT = env_path("LEANEUCLID_ROOT", WORKSPACE_ROOT / "LeanEuclid", WORKSPACE_ROOT)
OUT_PATH = SURVEY_DIR / "data" / "survey_data.json"
MAPPINGS_DIR = SURVEY_DIR / "line_sentence_mappings"
PREFERENCE_QUESTIONS_PATH = SURVEY_DIR / "preference_questions.json"
INCLUDE_LINE_SENTENCE_MAPPINGS = os.environ.get("SURVEY_INCLUDE_LINE_SENTENCE_MAPPINGS", "0") == "1"

BOOK = 1
NEW_METHOD_ID = "new_method"
OLD_METHOD_LABEL = os.environ.get("OLD_METHOD_LABEL", "Formalization A")
NEW_METHOD_LABEL = os.environ.get("NEW_METHOD_LABEL", "Formalization B")


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def clean_tex_inline(text: str) -> str:
    text = re.sub(r"%.*$", "", text, flags=re.M)
    text = text.replace("~", " ")
    text = re.sub(r"\\ref\{([^}]+)\}", r"\1", text)
    text = re.sub(r"\\(?:emph|textit|textbf)\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\[a-zA-Z]+\*?(?:\[[^\]]*\])?(?:\{[^{}]*\})?", "", text)
    text = text.replace("{", "").replace("}", "")
    return " ".join(text.split())


def parse_enumerated_references(path: Path, kind: str, label_prefix: str, title_prefix: str) -> dict[str, dict[str, Any]]:
    if not path.exists():
        return {}
    raw = read_text(path)
    pattern = re.compile(
        rf"\\item\s+\\label\{{{re.escape(label_prefix)}:(\d+)\}}\s*(.*?)(?=^\s*\\item\s+\\label|\s*\\end\{{enumerate\}})",
        re.S | re.M,
    )
    refs: dict[str, dict[str, Any]] = {}
    for match in pattern.finditer(raw):
        number = int(match.group(1))
        text = clean_tex_inline(match.group(2))
        ref_id = f"{kind}:{number}"
        refs[ref_id] = {
            "id": ref_id,
            "kind": kind,
            "number": number,
            "label": f"{title_prefix} {number}",
            "text": text,
            "source_path": path.relative_to(LEANEUCLID_PLUS).as_posix(),
        }
    return refs


def build_reference_index() -> dict[str, dict[str, Any]]:
    refs: dict[str, dict[str, Any]] = {}
    refs.update(parse_enumerated_references(LEANEUCLID_PLUS / "blueprint" / "src" / "common_notions.tex", "cn", "cn", "Common Notion"))
    refs.update(parse_enumerated_references(LEANEUCLID_PLUS / "blueprint" / "src" / "postulates.tex", "post", "post", "Postulate"))
    refs.update(parse_enumerated_references(LEANEUCLID_PLUS / "blueprint" / "src" / "definitions.tex", "def", "def", "Definition"))
    return refs


def code_lines(path: Path, root: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rel = path.relative_to(root).as_posix()
    return [
        {"line": i, "text": line.rstrip("\n"), "path": rel}
        for i, line in enumerate(read_text(path).splitlines(), start=1)
    ]


def parse_rubric(path: Path) -> list[dict[str, Any]]:
    raw = read_text(path)
    metric_heads = list(re.finditer(r"^## Metric (\d+): (.+)$", raw, re.M))
    metrics: list[dict[str, Any]] = []
    for idx, head in enumerate(metric_heads):
        number = int(head.group(1))
        title = head.group(2).strip()
        end = metric_heads[idx + 1].start() if idx + 1 < len(metric_heads) else raw.find("\n## Scoring Notes", head.end())
        if end == -1:
            end = len(raw)
        block = raw[head.end():end]
        prompt = ""
        for line in block.splitlines():
            clean = line.strip()
            if clean and not clean.startswith("Score guide"):
                prompt = clean
                break
        options = []
        for m in re.finditer(r"^- \*\*(\d+) - ([^*]+)\*\* (.+)$", block, re.M):
            options.append({
                "score": int(m.group(1)),
                "label": m.group(2).strip(),
                "standard": m.group(3).strip(),
            })
        metrics.append({
            "id": f"m{number}",
            "number": number,
            "title": title,
            "prompt": prompt,
            "score_options": options,
        })
    return metrics


def load_preference_questions(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {"version": 1, "questions": []}
    raw = json.loads(read_text(path))
    questions = []
    for idx, item in enumerate(raw.get("questions", []), start=1):
        question_id = str(item.get("id", "")).strip()
        if not question_id:
            continue
        questions.append({
            "id": question_id,
            "number": int(item.get("number", idx)),
            "title": str(item.get("title", "")).strip(),
            "prompt": str(item.get("prompt", "")).strip(),
        })
    return {
        "version": int(raw.get("version", 1)),
        "questions": questions,
    }


def proposition_intro_from_nodes(nodes: list[dict[str, Any]]) -> str:
    for node in nodes:
        if node.get("kind") == "structural" and str(node.get("loc", "")).endswith(".0"):
            return str(node.get("text", "")).strip()
    return ""


def parse_theorem_statement(lines: list[dict[str, Any]]) -> str:
    capture: list[str] = []
    seen = False
    for row in lines:
        text = row["text"]
        if text.strip().startswith("theorem proposition_"):
            seen = True
        if seen:
            capture.append(text)
            if ":= by" in text or text.strip() == "by":
                break
    return "\n".join(capture).strip()


def parse_imports(lines: list[dict[str, Any]]) -> list[str]:
    imports = []
    for row in lines:
        text = row["text"].strip()
        if text.startswith("import "):
            imports.append(text.removeprefix("import ").strip())
    return imports


def split_text_sentences(text: str) -> list[dict[str, Any]]:
    protected = {
        "Prop.~": "Prop§",
        "Post.~": "Post§",
        "C.N.~": "CN§",
        "C.N.": "CN§",
    }
    normalized = " ".join(text.split())
    for source, target in protected.items():
        normalized = normalized.replace(source, target)
    parts = re.split(r"(?<=[.!?])\s+", normalized)
    sentences = []
    for idx, part in enumerate((p.strip() for p in parts if p.strip()), start=1):
        for source, target in protected.items():
            part = part.replace(target, source)
        sentences.append({"id": f"s{idx}", "number": idx, "text": part})
    return sentences


def load_line_sentence_mappings(prop_id: str, text_sentences: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    path = MAPPINGS_DIR / f"{prop_id}.json"
    if not path.exists():
        return {}
    raw = json.loads(read_text(path))
    sentence_ids = {s["id"] for s in text_sentences}
    by_method: dict[str, list[dict[str, Any]]] = {}
    for idx, item in enumerate(raw.get("mappings", []), start=1):
        method_id = item.get("method_id", "")
        ranges = []
        for range_item in item.get("code_ranges", []):
            file = str(range_item.get("file", "")).strip()
            if not file:
                continue
            start = int(range_item.get("start_line", range_item.get("line", 0)))
            end = int(range_item.get("end_line", start))
            if start <= 0:
                continue
            ranges.append({"file": file, "start_line": start, "end_line": max(start, end)})
        sentences = []
        for sentence_id in item.get("sentence_ids", []):
            normalized = str(sentence_id).strip().lower()
            if normalized in sentence_ids:
                sentences.append(normalized)
        if not method_id or not ranges or not sentences:
            continue
        by_method.setdefault(method_id, []).append({
            "id": item.get("id") or f"{prop_id}_{method_id}_map_{idx}",
            "sentence_ids": sentences,
            "code_ranges": ranges,
            "relation": item.get("relation", ""),
            "rationale": item.get("rationale", ""),
        })
    return by_method


def parse_euclid_sentences(main_path: Path, root: Path) -> list[dict[str, Any]]:
    if not main_path.exists():
        return []
    src = read_text(main_path)
    rel = main_path.relative_to(root).as_posix()
    pattern = re.compile(
        r'euclid_(sentence|intro_sentence|conclude_sentence)\s+'
        r'"((?:[^"\\]|\\.)*)"\s+"((?:[^"\\]|\\.)*)"'
        r'(?:\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*:\s*)?',
        re.S,
    )
    nodes = []
    for m in pattern.finditer(src):
        kind_raw, loc, text, name = m.group(1), m.group(2), m.group(3), m.group(4)
        line = src.count("\n", 0, m.start()) + 1
        kind = "logical" if kind_raw == "sentence" else "structural"
        claim = ""
        if name:
            claim_start = m.end()
            depth = 1
            i = claim_start
            while i < len(src):
                ch = src[i]
                if ch == '"':
                    i += 1
                    while i < len(src) and src[i] != '"':
                        i += 2 if src[i] == "\\" else 1
                elif ch == "(":
                    depth += 1
                elif ch == ")":
                    depth -= 1
                    if depth == 0:
                        claim = " ".join(src[claim_start:i].split())
                        break
                i += 1
        nodes.append({
            "loc": loc,
            "kind": kind,
            "name": name or "",
            "text": text.replace('\\"', '"'),
            "claim": claim,
            "file": rel,
            "line": line,
        })
    return sorted(nodes, key=lambda n: [int(x) for x in n["loc"].split(".") if x.isdigit()])


def parse_dependency_tokens(lines: list[dict[str, Any]]) -> list[dict[str, Any]]:
    deps = []
    seen = set()
    patterns = [
        (r"proposition_(\d+)", "proposition"),
        (r"line_from_points", "postulate"),
        (r"area_congruence|sum_areas_if", "area"),
        (r"euclid_finish", "automation"),
    ]
    for row in lines:
        text = row["text"]
        for pat, kind in patterns:
            for m in re.finditer(pat, text):
                label = m.group(0)
                key = (kind, label, row["path"], row["line"])
                if key in seen:
                    continue
                seen.add(key)
                deps.append({"kind": kind, "label": label, "file": row["path"], "line": row["line"]})
    return deps


def method_payload(method_id: str, label: str, root: Path, files: list[Path], line_text_mappings: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    existing = [p for p in files if p.exists()]
    all_lines: list[dict[str, Any]] = []
    file_payloads = []
    for p in existing:
        lines = code_lines(p, root)
        all_lines.extend(lines)
        file_payloads.append({"path": p.relative_to(root).as_posix(), "lines": lines})
    main_lines = file_payloads[0]["lines"] if file_payloads else []
    main_path = existing[0] if existing else None
    return {
        "id": method_id,
        "label": label,
        "available": bool(existing),
        "root": str(root),
        "files": file_payloads,
        "theorem_statement": parse_theorem_statement(main_lines),
        "imports": parse_imports(main_lines),
        "proof_nodes": parse_euclid_sentences(main_path, root) if main_path and main_path.name == "Main.lean" else [],
        "dependencies": parse_dependency_tokens(all_lines),
        "line_text_mappings": line_text_mappings or [],
    }


def prop_title(text: str, number: int) -> str:
    first = text.strip().split(".")[0].strip()
    if len(first) > 110:
        first = first[:107].rstrip() + "..."
    return first or f"Proposition {number}"


def build() -> dict[str, Any]:
    rubric = parse_rubric(LEANEUCLID_PLUS / "eval" / "faithfulness_rubric.md")
    preference_questions = load_preference_questions(PREFERENCE_QUESTIONS_PATH)
    references = build_reference_index()
    propositions = []
    for text_path in sorted((LEANEUCLID_PLUS / "Book1" / "data" / "texts_proofs").glob("*.txt"), key=lambda p: int(p.stem)):
        number = int(text_path.stem)
        prop_num = f"{number:02d}"
        text = read_text(text_path).strip()
        text_sentences = split_text_sentences(text)
        mappings = load_line_sentence_mappings(f"book1_prop{prop_num}", text_sentences) if INCLUDE_LINE_SENTENCE_MAPPINGS else {}
        old_file = LEANEUCLID_ROOT / "Book" / f"Prop{prop_num}.lean"
        new_dir = LEANEUCLID_PLUS / "Book1" / f"Prop{prop_num}"
        new_files = [new_dir / "Main.lean"] + sorted(p for p in new_dir.glob("*.lean") if p.name != "Main.lean")
        diagram = LEANEUCLID_PLUS / "Book1" / "data" / "diagrams" / f"{number}.png"
        old_method = method_payload("leaneuclid", OLD_METHOD_LABEL, LEANEUCLID_ROOT, [old_file], mappings.get("leaneuclid"))
        new_method = method_payload(NEW_METHOD_ID, NEW_METHOD_LABEL, LEANEUCLID_PLUS, new_files, mappings.get(NEW_METHOD_ID))
        proposition_text = proposition_intro_from_nodes(new_method.get("proof_nodes", []))
        proposition_sentence_count = len(split_text_sentences(proposition_text)) if proposition_text else 1
        proof_text = " ".join(sentence["text"] for sentence in text_sentences[proposition_sentence_count:]).strip()
        propositions.append({
            "id": f"book1_prop{prop_num}",
            "book": 1,
            "number": number,
            "display": f"Book I, Proposition {number}",
            "title": prop_title(text, number),
            "text": text,
            "proposition_text": proposition_text or (text_sentences[0]["text"] if text_sentences else ""),
            "proof_text": proof_text,
            "text_sentences": text_sentences,
            "diagram": {
                "available": diagram.exists(),
                "path": f"/api/assets/diagrams/{number}.png",
                "source_path": diagram.relative_to(LEANEUCLID_PLUS).as_posix() if diagram.exists() else "",
            },
            "methods": {
                "leaneuclid": old_method,
                NEW_METHOD_ID: new_method,
            },
        })
    return {
        "version": 1,
        "generated_from": {
            "leaneuclid_plus": str(LEANEUCLID_PLUS),
            "leaneuclid": str(LEANEUCLID_ROOT),
        },
        "methods": [
            {"id": "leaneuclid", "label": OLD_METHOD_LABEL},
            {"id": NEW_METHOD_ID, "label": NEW_METHOD_LABEL},
        ],
        "rubric": {"scale_min": 0, "scale_max": 5, "metrics": rubric},
        "preference_questions": preference_questions,
        "references": references,
        "propositions": propositions,
    }


def main() -> int:
    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    data = build()
    OUT_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
    ready = sum(1 for p in data["propositions"] if all(m["available"] for m in p["methods"].values()))
    print(f"wrote {OUT_PATH.relative_to(LEANEUCLID_PLUS)}")
    print(f"propositions: {len(data['propositions'])}; ready pairs: {ready}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
