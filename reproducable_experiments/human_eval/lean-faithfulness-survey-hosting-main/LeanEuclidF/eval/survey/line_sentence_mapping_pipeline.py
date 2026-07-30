#!/usr/bin/env python3
"""One-command pipeline for Lean-line to textbook-sentence mappings.

The pipeline standardizes the repeatable parts:

1. Build a proposition context with textbook sentence IDs and Lean files.
2. Build a deterministic prompt for Codex, Claude Code, or another command.
3. Optionally run that agent and parse a JSON mapping from its output.
4. Validate and canonicalize the mapping JSON.
5. Regenerate survey_data.json so the website can render the badges.

Without an agent, this command still prepares the context/prompt and validates an
existing mapping file if present.
"""

from __future__ import annotations

import argparse
import json
import re
import shlex
import shutil
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

import extract_survey_data as ex


GENERATED_DIR = ex.MAPPINGS_DIR / "generated"
VALID_RELATIONS = {"one-to-one", "one-to-many", "many-to-one", "many-to-many"}
METHOD_IDS = ("leaneuclid", ex.NEW_METHOD_ID)


@dataclass
class PipelinePaths:
    prop_id: str
    mapping: Path
    context: Path
    prompt: Path
    response: Path
    report: Path


@dataclass
class PipelineResult:
    prop_id: str
    status: str
    warnings: int = 0
    message: str = ""


def prop_id_from_number(number: int) -> str:
    return f"book1_prop{number:02d}"


def available_proposition_numbers() -> list[int]:
    text_dir = ex.LEANEUCLID_PLUS / "Book1" / "data" / "texts_proofs"
    return sorted(int(path.stem) for path in text_dir.glob("*.txt") if path.stem.isdigit())


def paths_for(prop_id: str) -> PipelinePaths:
    GENERATED_DIR.mkdir(parents=True, exist_ok=True)
    return PipelinePaths(
        prop_id=prop_id,
        mapping=ex.MAPPINGS_DIR / f"{prop_id}.json",
        context=GENERATED_DIR / f"{prop_id}_context.md",
        prompt=GENERATED_DIR / f"{prop_id}_prompt.md",
        response=GENERATED_DIR / f"{prop_id}_agent_response.txt",
        report=GENERATED_DIR / f"{prop_id}_validation.md",
    )


def numbered_lines(lines: list[dict[str, Any]]) -> str:
    return "\n".join(f"{row['line']:>4}  {row['text']}" for row in lines)


def proposition_payload(number: int) -> dict[str, Any]:
    prop_id = prop_id_from_number(number)
    text_path = ex.LEANEUCLID_PLUS / "Book1" / "data" / "texts_proofs" / f"{number}.txt"
    if not text_path.exists():
        raise FileNotFoundError(f"Missing textbook proof file: {text_path}")

    text = ex.read_text(text_path).strip()
    text_sentences = ex.split_text_sentences(text)
    prop_num = f"{number:02d}"
    old_file = ex.LEANEUCLID_ROOT / "Book" / f"Prop{prop_num}.lean"
    new_dir = ex.LEANEUCLID_PLUS / "Book1" / f"Prop{prop_num}"
    new_files = [new_dir / "Main.lean"] + sorted(p for p in new_dir.glob("*.lean") if p.name != "Main.lean")
    return {
        "id": prop_id,
        "number": number,
        "text": text,
        "text_sentences": text_sentences,
        "methods": {
            "leaneuclid": ex.method_payload("leaneuclid", "LeanEuclid", ex.LEANEUCLID_ROOT, [old_file]),
            ex.NEW_METHOD_ID: ex.method_payload(ex.NEW_METHOD_ID, ex.NEW_METHOD_LABEL, ex.LEANEUCLID_PLUS, new_files),
        },
    }


def build_context(prop: dict[str, Any]) -> str:
    parts = [
        f"# Mapping Context: {prop['id']}",
        "",
        "## Textbook Sentences",
        "",
    ]
    for sentence in prop["text_sentences"]:
        parts.append(f"- **{sentence['id']}** {sentence['text']}")
    parts.extend(["", "## Lean Formalizations", ""])

    for method_id in METHOD_IDS:
        method = prop["methods"][method_id]
        parts.extend([
            f"### {method['label']} (`{method_id}`)",
            "",
            f"Available: `{str(method['available']).lower()}`",
            "",
        ])
        if not method["available"]:
            parts.append("No source file is available for this method/proposition yet.")
            parts.append("")
            continue
        if method.get("proof_nodes"):
            parts.extend(["#### Extracted Euclid Sentence Nodes", ""])
            for node in method["proof_nodes"]:
                claim = f" Claim: `{node['claim']}`" if node.get("claim") else ""
                parts.append(f"- `{node['loc']}` `{node['file']}:{node['line']}` {node['text']}{claim}")
            parts.append("")
        for file in method["files"]:
            parts.extend([
                f"#### `{file['path']}`",
                "",
                "```lean",
                numbered_lines(file["lines"]),
                "```",
                "",
            ])
    return "\n".join(parts).rstrip() + "\n"


def build_prompt(prop: dict[str, Any], context: str) -> str:
    example_id = f"{prop['id']}-example"
    return f"""You are creating Lean-code-line to textbook-sentence mappings for a Euclid formalization survey.

Return only valid JSON. Do not include markdown fences or commentary.

Schema:
{{
  "version": 1,
  "proposition_id": "{prop['id']}",
  "mappings": [
    {{
      "id": "{example_id}",
      "method_id": "leaneuclid",
      "sentence_ids": ["s1"],
      "code_ranges": [
        {{ "file": "Book/Prop{prop['number']:02d}.lean", "start_line": 1, "end_line": 1 }}
      ],
      "relation": "one-to-one",
      "rationale": "Concise mathematical reason."
    }}
  ]
}}

Mapping standard:
- Prefer the most atomic faithful mapping.
- Use one Lean line to one textbook sentence when the correspondence is clear.
- If multiple nearby Lean lines or helper-file lines together implement the same sentence, put those ranges in one mapping so they share one label.
- If one Lean line compresses several textbook sentences, map that line to those sentence IDs.
- Use many-to-many only when the code genuinely packages a larger proof block, such as an omitted symmetric branch.
- Leave administrative lines unmapped: imports, namespace/end, options, and code with no meaningful mathematical correspondence.
- Do not map comments unless they are the only representation of a mathematical step.
- Use only files, line numbers, sentence IDs, and method IDs present in the context below.
- The allowed method_id values are "leaneuclid" and "{ex.NEW_METHOD_ID}".

{context}
"""


def extract_json_object(text: str) -> dict[str, Any]:
    stripped = text.strip()
    fenced = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", stripped, re.S)
    if fenced:
        stripped = fenced.group(1).strip()
    try:
        parsed = json.loads(stripped)
        if isinstance(parsed, dict):
            return parsed
    except json.JSONDecodeError:
        pass

    decoder = json.JSONDecoder()
    for match in re.finditer(r"\{", stripped):
        try:
            parsed, _ = decoder.raw_decode(stripped[match.start():])
        except json.JSONDecodeError:
            continue
        if isinstance(parsed, dict) and parsed.get("mappings") is not None:
            return parsed
    raise ValueError("Agent output did not contain a mapping JSON object")


def command_for_agent(agent: str, custom_cmd: str | None) -> list[str] | None:
    if custom_cmd:
        return shlex.split(custom_cmd)
    if agent == "none":
        return None
    if agent == "codex":
        if not shutil.which("codex"):
            raise RuntimeError("codex command not found; use --agent none or --agent-cmd")
        return ["codex", "exec", "-"]
    if agent == "claude":
        if not shutil.which("claude"):
            raise RuntimeError("claude command not found; use --agent none or --agent-cmd")
        return ["claude", "-p"]
    raise ValueError(f"Unknown agent: {agent}")


def run_agent(prompt: str, agent: str, custom_cmd: str | None) -> str:
    cmd = command_for_agent(agent, custom_cmd)
    if not cmd:
        raise ValueError("No agent command configured")
    proc = subprocess.run(
        cmd,
        input=prompt,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        cwd=ex.LEANEUCLID_PLUS,
        check=False,
    )
    output = proc.stdout.strip()
    if proc.stderr.strip():
        output = f"{output}\n\n[stderr]\n{proc.stderr.strip()}".strip()
    if proc.returncode != 0:
        raise RuntimeError(f"Agent command exited with code {proc.returncode}. Output saved for inspection.")
    return output


def method_file_index(prop: dict[str, Any]) -> dict[str, dict[str, int]]:
    index: dict[str, dict[str, int]] = {}
    for method_id, method in prop["methods"].items():
        index[method_id] = {file["path"]: len(file["lines"]) for file in method["files"]}
    return index


def canonical_mapping(raw: dict[str, Any], prop: dict[str, Any]) -> tuple[dict[str, Any], list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    prop_id = prop["id"]
    sentence_ids = {s["id"] for s in prop["text_sentences"]}
    files = method_file_index(prop)

    if raw.get("proposition_id") != prop_id:
        errors.append(f"proposition_id must be {prop_id!r}, found {raw.get('proposition_id')!r}")

    seen_ids: set[str] = set()
    clean_items = []
    for idx, item in enumerate(raw.get("mappings", []), start=1):
        item_id = str(item.get("id") or f"{prop_id}_mapping_{idx}").strip()
        if item_id in seen_ids:
            errors.append(f"duplicate mapping id: {item_id}")
        seen_ids.add(item_id)

        method_id = str(item.get("method_id", "")).strip()
        if method_id not in METHOD_IDS:
            errors.append(f"{item_id}: invalid method_id {method_id!r}")

        clean_sentences = []
        for sentence_id in item.get("sentence_ids", []):
            sid = str(sentence_id).strip().lower()
            if sid not in sentence_ids:
                errors.append(f"{item_id}: unknown sentence id {sentence_id!r}")
            elif sid not in clean_sentences:
                clean_sentences.append(sid)
        if not clean_sentences:
            errors.append(f"{item_id}: sentence_ids is empty")

        clean_ranges = []
        for range_idx, range_item in enumerate(item.get("code_ranges", []), start=1):
            file = str(range_item.get("file", "")).strip()
            try:
                start = int(range_item.get("start_line", range_item.get("line", 0)))
                end = int(range_item.get("end_line", start))
            except (TypeError, ValueError):
                errors.append(f"{item_id}: range {range_idx} has non-integer line numbers")
                continue
            if method_id in files and file not in files[method_id]:
                errors.append(f"{item_id}: file {file!r} is not available for method {method_id!r}")
                continue
            max_line = files.get(method_id, {}).get(file, 0)
            if start <= 0 or end < start or (max_line and end > max_line):
                errors.append(f"{item_id}: invalid range {file}:{start}-{end}; file has {max_line} lines")
                continue
            clean_ranges.append({"file": file, "start_line": start, "end_line": end})
        if not clean_ranges:
            errors.append(f"{item_id}: code_ranges is empty")

        relation = str(item.get("relation", "")).strip()
        inferred = infer_relation(clean_sentences, clean_ranges)
        if relation not in VALID_RELATIONS:
            warnings.append(f"{item_id}: relation {relation!r} replaced with inferred {inferred!r}")
            relation = inferred
        elif relation != inferred:
            warnings.append(f"{item_id}: relation is {relation!r}; inferred shape is {inferred!r}")

        if relation == "many-to-many":
            sentence_count = len(clean_sentences)
            range_count = sum(r["end_line"] - r["start_line"] + 1 for r in clean_ranges)
            if sentence_count > 2 and range_count > 4:
                warnings.append(f"{item_id}: broad many-to-many mapping; keep only if this is genuinely packaged proof code")

        clean_items.append({
            "id": item_id,
            "method_id": method_id,
            "sentence_ids": clean_sentences,
            "code_ranges": clean_ranges,
            "relation": relation,
            "rationale": str(item.get("rationale", "")).strip(),
        })

    clean_items, overlap_warnings = merge_overlapping_mappings(prop_id, clean_items)
    warnings.extend(overlap_warnings)
    canonical = {"version": 1, "proposition_id": prop_id, "mappings": clean_items}
    return canonical, errors, warnings


def merge_overlapping_mappings(prop_id: str, items: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[str]]:
    warnings: list[str] = []
    current = items
    while True:
        changed = False
        next_items: list[dict[str, Any]] = []
        used: set[int] = set()

        for idx, item in enumerate(current):
            if idx in used:
                continue
            group_indices = overlap_component(idx, current, used)
            if len(group_indices) == 1:
                next_items.append(item)
                used.add(idx)
                continue

            group = [current[i] for i in group_indices]
            merged = merge_mapping_group(prop_id, group)
            next_items.append(merged)
            used.update(group_indices)
            changed = True
            merged_ids = ", ".join(g["id"] for g in group)
            warnings.append(f"{merged['id']}: merged overlapping mappings: {merged_ids}")

        current = next_items
        if not changed:
            return current, warnings


def overlap_component(start_idx: int, items: list[dict[str, Any]], already_used: set[int]) -> list[int]:
    component = {start_idx}
    queue = [start_idx]
    while queue:
        idx = queue.pop()
        for other_idx, other in enumerate(items):
            if other_idx in already_used or other_idx in component:
                continue
            if mappings_overlap(items[idx], other):
                component.add(other_idx)
                queue.append(other_idx)
    return sorted(component)


def mappings_overlap(left: dict[str, Any], right: dict[str, Any]) -> bool:
    if left["method_id"] != right["method_id"]:
        return False
    for left_range in left["code_ranges"]:
        for right_range in right["code_ranges"]:
            if ranges_overlap(left_range, right_range):
                return True
    return False


def ranges_overlap(left: dict[str, int], right: dict[str, int]) -> bool:
    if left["file"] != right["file"]:
        return False
    return max(left["start_line"], right["start_line"]) <= min(left["end_line"], right["end_line"])


def merge_mapping_group(prop_id: str, group: list[dict[str, Any]]) -> dict[str, Any]:
    method_id = group[0]["method_id"]
    sentence_ids: list[str] = []
    rationales: list[str] = []
    ranges: list[dict[str, int]] = []
    for item in group:
        for sentence_id in item["sentence_ids"]:
            if sentence_id not in sentence_ids:
                sentence_ids.append(sentence_id)
        rationale = item.get("rationale", "").strip()
        if rationale and rationale not in rationales:
            rationales.append(rationale)
        ranges.extend(item["code_ranges"])

    merged_ranges = merge_ranges(ranges)
    first_id = group[0]["id"]
    suffix = re.sub(r"[^A-Za-z0-9_]+", "_", first_id).strip("_")
    item_id = f"{prop_id}_{method_id}_merged_{suffix}"
    return {
        "id": item_id,
        "method_id": method_id,
        "sentence_ids": sentence_ids,
        "code_ranges": merged_ranges,
        "relation": infer_relation(sentence_ids, merged_ranges),
        "rationale": " / ".join(rationales),
    }


def merge_ranges(ranges: list[dict[str, int]]) -> list[dict[str, int]]:
    by_file: dict[str, list[dict[str, int]]] = {}
    for range_item in ranges:
        by_file.setdefault(range_item["file"], []).append(range_item)

    merged: list[dict[str, int]] = []
    for file, file_ranges in by_file.items():
        ordered = sorted(file_ranges, key=lambda r: (r["start_line"], r["end_line"]))
        current: dict[str, int] | None = None
        for range_item in ordered:
            if current and range_item["start_line"] <= current["end_line"] + 1:
                current["end_line"] = max(current["end_line"], range_item["end_line"])
                continue
            if current:
                merged.append(current)
            current = {"file": file, "start_line": range_item["start_line"], "end_line": range_item["end_line"]}
        if current:
            merged.append(current)
    return sorted(merged, key=lambda r: (r["file"], r["start_line"], r["end_line"]))


def infer_relation(sentence_ids: list[str], ranges: list[dict[str, int]]) -> str:
    sentence_count = len(sentence_ids)
    line_count = sum(r["end_line"] - r["start_line"] + 1 for r in ranges)
    if sentence_count <= 1 and line_count <= 1:
        return "one-to-one"
    if sentence_count <= 1:
        return "one-to-many"
    if line_count <= 1:
        return "many-to-one"
    return "many-to-many"


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def write_report(path: Path, prop_id: str, errors: list[str], warnings: list[str]) -> None:
    lines = [f"# Mapping Validation Report: {prop_id}", ""]
    if errors:
        lines.extend(["## Errors", ""])
        lines.extend(f"- {err}" for err in errors)
        lines.append("")
    if warnings:
        lines.extend(["## Warnings", ""])
        lines.extend(f"- {warn}" for warn in warnings)
        lines.append("")
    if not errors and not warnings:
        lines.extend(["No errors or warnings.", ""])
    path.write_text("\n".join(lines), encoding="utf-8")


def load_existing_mapping(path: Path) -> dict[str, Any]:
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    raise FileNotFoundError(path)


def run_extract() -> None:
    data = ex.build()
    ex.OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    ex.OUT_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")


def run_one_prop(args: argparse.Namespace, number: int, extract: bool = True) -> PipelineResult:
    prop = proposition_payload(number)
    paths = paths_for(prop["id"])

    context = build_context(prop)
    prompt = build_prompt(prop, context)
    paths.context.write_text(context, encoding="utf-8")
    paths.prompt.write_text(prompt, encoding="utf-8")

    generated = False
    if args.agent != "none" or args.agent_cmd:
        if paths.mapping.exists() and not args.overwrite:
            return PipelineResult(prop["id"], "skipped", message=f"mapping exists: {paths.mapping.relative_to(ex.LEANEUCLID_PLUS)}")
        output = run_agent(prompt, args.agent, args.agent_cmd)
        paths.response.write_text(output + "\n", encoding="utf-8")
        raw = extract_json_object(output)
        generated = True
    else:
        if not paths.mapping.exists():
            paths.report.write_text(
                "\n".join([
                    f"# Mapping Validation Report: {prop['id']}",
                    "",
                    "No mapping file exists yet.",
                    "",
                    f"Context: `{paths.context.relative_to(ex.LEANEUCLID_PLUS)}`",
                    f"Prompt: `{paths.prompt.relative_to(ex.LEANEUCLID_PLUS)}`",
                    "",
                    "Run again with `--agent codex`, `--agent claude`, or `--agent-cmd ...` to generate the mapping in one command.",
                ]),
                encoding="utf-8",
            )
            return PipelineResult(prop["id"], "missing", message=f"mapping missing: {paths.mapping.relative_to(ex.LEANEUCLID_PLUS)}")
        raw = load_existing_mapping(paths.mapping)

    canonical, errors, warnings = canonical_mapping(raw, prop)
    write_report(paths.report, prop["id"], errors, warnings)
    if errors:
        return PipelineResult(prop["id"], "failed", len(warnings), f"validation failed: {paths.report.relative_to(ex.LEANEUCLID_PLUS)}")

    write_json(paths.mapping, canonical)
    if extract:
        run_extract()

    action = "generated" if generated else "validated"
    return PipelineResult(
        prop["id"],
        action,
        len(warnings),
        f"{action} {paths.mapping.relative_to(ex.LEANEUCLID_PLUS)}",
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate, validate, and publish Lean-line/textbook-sentence mappings.")
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--prop", type=int, help="Book I proposition number, e.g. 6")
    target.add_argument("--all", action="store_true", help="Run over every available Book I proposition")
    target.add_argument("--props", help="Comma-separated proposition numbers or ranges, e.g. 1,3,7-10")
    parser.add_argument("--agent", choices=["none", "codex", "claude"], default="none", help="Optional agent to run")
    parser.add_argument("--agent-cmd", help="Custom command that reads the prompt on stdin and writes JSON on stdout")
    parser.add_argument("--overwrite", action="store_true", help="Overwrite existing mapping files instead of skipping them")
    parser.add_argument("--no-extract", action="store_true", help="Skip regenerating survey_data.json after validation")
    return parser.parse_args(argv)


def parse_prop_list(spec: str) -> list[int]:
    numbers: set[int] = set()
    for part in spec.split(","):
        item = part.strip()
        if not item:
            continue
        if "-" in item:
            start_raw, end_raw = item.split("-", 1)
            start = int(start_raw)
            end = int(end_raw)
            if end < start:
                raise ValueError(f"invalid proposition range: {item}")
            numbers.update(range(start, end + 1))
        else:
            numbers.add(int(item))
    return sorted(numbers)


def target_numbers(args: argparse.Namespace) -> list[int]:
    if args.all:
        return available_proposition_numbers()
    if args.props:
        return parse_prop_list(args.props)
    return [args.prop]


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv or sys.argv[1:])
    numbers = target_numbers(args)
    total = len(numbers)
    results: list[PipelineResult] = []
    had_failure = False

    agent_enabled = args.agent != "none" or bool(args.agent_cmd)
    if agent_enabled and args.overwrite:
        print("overwrite enabled: existing mapping files will be regenerated")
    elif agent_enabled:
        print("skip-existing enabled: existing mapping files will be skipped")
    else:
        print("validation mode: existing mapping files will be validated; missing files will be reported")

    for index, number in enumerate(numbers, start=1):
        prop_id = prop_id_from_number(number)
        print(f"[{index}/{total}] {prop_id}: start", flush=True)
        try:
            result = run_one_prop(args, number, extract=False)
        except Exception as exc:
            result = PipelineResult(prop_id, "failed", message=str(exc))
        results.append(result)

        suffix = f" ({result.message})" if result.message else ""
        warning_text = f"; warnings={result.warnings}" if result.warnings else ""
        print(f"[{index}/{total}] {prop_id}: {result.status}{warning_text}{suffix}", flush=True)

        if result.status == "failed":
            had_failure = True
            break

    if not args.no_extract:
        print("regenerating survey data", flush=True)
        run_extract()
        print(f"updated {ex.OUT_PATH.relative_to(ex.LEANEUCLID_PLUS)}", flush=True)

    counts: dict[str, int] = {}
    for result in results:
        counts[result.status] = counts.get(result.status, 0) + 1
    summary = ", ".join(f"{key}={counts[key]}" for key in sorted(counts))
    print(f"summary: {summary or 'none'}")
    return 1 if had_failure else 0


if __name__ == "__main__":
    raise SystemExit(main())
