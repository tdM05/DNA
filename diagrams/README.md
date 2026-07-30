# Proof-map visualizer

`scripts/proof_map.py` renders a faithful LeanEuclidPlus proof as an interactive HTML **map**:
one card per Euclid sentence, with its backing `have`/`stepN.lean` lemmas nested as children, so
the sentence-to-formal-step structure is visible and navigable. It is a **visualization aid for
inspecting the artifacts** — not part of the proving pipeline.

> **Pre-generated for every proposition.** A ready-to-open `map.html` already ships in each
> `LeanEuclidPlus/Book<N>/Prop<NN>/` folder — just open one in a browser, no toolchain or Python
> needed. The steps below are only for regenerating them.

## Generate a map

Run from the repo root (or `LeanEuclidPlus/`):

```bash
python3 diagrams/scripts/proof_map.py --prop Book1/Prop06        # -> Book1/Prop06/map.html
python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 -o out.html
```

`--prop` takes `Book<N>/Prop<NN>`; it is resolved under `LeanEuclidPlus/` automatically. The map is
built by reading `Main.lean` and each `stepN.lean` backing file directly (following the
`stepN` ↔ `stepN.lean` naming law), so the card nesting reflects the proof's actual backing-lemma
structure.

Open the resulting `map.html` in any browser — it is a single self-contained file.

## Using the map

- **Cards** = one Euclid sentence (teal) or a backing `have`/lemma (orange), nested by the real
  file structure; **drag** cards to rearrange.
- **Connectors** link each sentence/`have` line to the card that proves it (the backing-lemma edges).
- **Left-click a line** — highlight everywhere that step's claim/name recurs ("who uses this"),
  drawing reference arrows. (This is a *textual* match on the shown claim type / step name — a
  presentation aid, not a term-level dependency resolver.)
- **Click the ▸ badge** on a sentence, or the card header, to cycle detail level (minimal ↔ full);
  folded `(N hyps ▸)` badges expand the assumptions.
- **Toolbar sliders**: font size, row height, connector gap, and **Max width** (card wrap width,
  default 300 px). Toggles: hide comments, collapse whitespace, sorry-only view.
- **Save layout** downloads `map_layout.json`; move it into the prop folder to persist an
  arrangement and to drive PNG export.

## Export to PNG (optional)

Needs Playwright once: `pip install playwright && playwright install chromium`. Then, with a saved
`map_layout.json` in the prop folder:

```bash
python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 --png          # -> map.png
python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 --all_layouts  # one PNG per map_layout*.json
```

`--scale N` (default 2) and `--transparent` are also accepted.
