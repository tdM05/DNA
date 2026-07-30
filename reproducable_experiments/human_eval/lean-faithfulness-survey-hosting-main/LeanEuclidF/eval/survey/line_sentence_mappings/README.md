# Lean Line To Textbook Sentence Mappings

Each file in this directory is a source annotation file for one proposition:

```text
book1_prop06.json
```

The extractor reads these files and stores normalized mappings in `eval/survey/data/survey_data.json` under each method's `line_text_mappings` field.

## Schema

```json
{
  "version": 1,
  "proposition_id": "book1_prop06",
  "mappings": [
    {
      "id": "short-stable-id",
      "method_id": "leaneuclid",
      "sentence_ids": ["s1", "s2"],
      "code_ranges": [
        { "file": "Book/Prop06.lean", "start_line": 7, "end_line": 11 }
      ],
      "relation": "many-to-many",
      "rationale": "Why this Lean range corresponds to the textbook sentence(s)."
    }
  ]
}
```

`sentence_ids` refer to the automatically extracted textbook sentences for the proposition, numbered `s1`, `s2`, etc. `code_ranges` can point to one line, a contiguous line range, or several ranges across files. This supports one-to-one, one-to-many, many-to-one, and many-to-many mappings.

Prefer the most atomic faithful mapping:

- Use one Lean line to one textbook sentence when the correspondence is clear.
- If one textbook sentence is implemented by several nearby Lean lines or helper-file lines, put those ranges in one mapping so they share one sentence label.
- If one Lean line compresses several textbook sentences, use one mapping from that line to those sentence IDs.
- Use many-to-many mappings only when the proof step is genuinely packaged together, such as a symmetric helper that mirrors a whole omitted branch.
- Leave administrative lines unmapped when they do not carry a meaningful mathematical correspondence. Do not force every line to have a label.

## Prompt Template For Codex Or Claude Code

The preferred entry point is the one-command pipeline:

```bash
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 7
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 7 --agent codex
python3 eval/survey/line_sentence_mapping_pipeline.py --prop 7 --agent claude
python3 eval/survey/line_sentence_mapping_pipeline.py --all --agent codex
python3 eval/survey/line_sentence_mapping_pipeline.py --props 1,3,7-10 --agent codex
```

The no-agent form writes context and prompt files under `eval/survey/line_sentence_mappings/generated/`, validates any existing mapping file, and regenerates survey data. The agent forms additionally ask the installed command-line agent to return JSON and then validate/canonicalize it.

Existing mapping files are skipped by default during agent runs. Pass `--overwrite` to regenerate existing mappings intentionally. The command prints one progress line per proposition and a final summary.

Use this prompt when creating a mapping for another proposition:

```text
Create eval/survey/line_sentence_mappings/book1_propXX.json.

Use the textbook proof at Book1/data/texts_proofs/XX.txt and the Lean files for both methods.
Split the textbook proof into natural sentence IDs s1, s2, ... in the same order as the extractor.
Map Lean code ranges to the sentence IDs they formalize. Prefer the most atomic faithful correspondence over fixed line granularity. Do not force every Lean line to be mapped.

For each mapping, include:
- id: stable kebab-case identifier
- method_id: "leaneuclid" or "new_method"
- sentence_ids: one or more sentence IDs
- code_ranges: one or more file/start_line/end_line ranges
- relation: one-to-one, one-to-many, many-to-one, or many-to-many
- rationale: concise mathematical justification

Do not map comments or imports unless they materially establish the theorem/proof structure.
Do not force a mapping for purely administrative code.
If multiple code ranges together implement the same sentence or sentence group, put them in a single mapping so the website shows a shared label for all of them.
For a contiguous multi-line range, the website renders one continuous segmented badge through the covered lines, with the text label shown at the start of the range. Hovering any segment shows the same mapping and highlights the full range.
```
