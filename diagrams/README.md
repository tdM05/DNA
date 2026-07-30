# Proof-map visualizer

`scripts/proof_map.py` renders a faithful LeanEuclidF proof as an interactive HTML **map**:
one card per Euclid sentence, with its backing `have`/`stepN.lean` lemmas nested as children, so
the sentence-to-formal-step structure is visible and navigable. It is a **visualization aid for
inspecting the artifacts** — not part of the proving pipeline.

> **Pre-generated for every proposition.** A ready-to-open `map.html` already ships in each
> `LeanEuclidF/Book<N>/Prop<NN>/` folder — just open one in a browser, no toolchain or Python
> needed. The steps below are only for regenerating them.

## Generate a map

Run from the repo root (or `LeanEuclidF/`):

```bash
python3 diagrams/scripts/proof_map.py --prop Book1/Prop06        # -> Book1/Prop06/map.html
python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 -o out.html
```

`--prop` takes `Book<N>/Prop<NN>`; it is resolved under `LeanEuclidF/` automatically. The map is
built by reading `Main.lean` and each `stepN.lean` backing file directly (following the
`stepN` ↔ `stepN.lean` naming law), so the card nesting reflects the proof's actual backing-lemma
structure.

Open the resulting `map.html` in any browser — it is a single self-contained file.

## Using the map

Each **card** is one `.lean` file: teal = a Euclid sentence's step (from `Main.lean`), orange = a
backing `have`/`stepN.lean` lemma. Cards nest by the real file structure. There are two things you
interact with — a card's **header bar**, and individual **code lines** — and each responds to
*where* you click.

**Card header** (`<name>.lean`, three zones — drag it anywhere to reposition the card):

- **◀ left zone** — highlight this card's **parents**: the cards/lines that *consume* this one (who
  depends on it), with the incoming edges lit.
- **center (the name)** — cycle this card's **detail level**: full → compact (signatures only) →
  minimal (collapsed to a title), and back.
- **▶ right zone** — highlight this card's **children**: the backing lemmas it *depends on*, with
  the outgoing edges lit.
- Ctrl/Cmd-click a zone to add to the current selection (multi-select); rubber-band drag on empty
  canvas selects a group.

**Code lines** — click the **left half** vs the **right half** of a line for two different actions,
and the left-half action differs by line type:

- **Left half of a `have`/backing line** → **"who uses this"**: highlights every line whose text
  invokes this step (by its shown claim type or its `stepN` name) and draws reference arrows to them.
  *This is a textual match on the rendered `show TYPE;` / step name — a navigation aid, not a
  term-level dependency resolver.*
- **Left half of a sentence line** → cycle that **sentence's** display: full Lean → the NL text
  only → just the locator number → back (independent of the card-level detail cycle).
- **Right half of any backed line** → **select the line and jump to the card that proves it**
  (lights the connector to that backing card). Ctrl/Cmd-click to select several; click empty canvas
  to clear.

**Folded assumptions**: a `(N hyps ▸)` badge on a line hides that step's `euclid_assumption`
hypotheses — click it to expand (▾) / re-fold. (Expanded state is saved with the layout, so an
exported PNG keeps whatever you opened.)

**Toolbar** — global controls across the top:

- Per-card detail buttons **Full / Compact / Minimal** and per-sentence **Full / NL / Min** apply
  the corresponding level to *every* card/sentence at once.
- Toggles: **Comments** (hide `--` comments), **Spaces** (collapse whitespace), **Sorry**
  (sorry-only view).
- Sliders: font size, row height, connector gap, and **Max width** (card wrap width, default
  300 px).
- **Save layout** downloads `map_layout.json` (also drives PNG export); **Import layout** reloads a
  saved one; **Reset** restores defaults.

## Export to PNG (optional)

Needs Playwright once: `pip install playwright && playwright install chromium`. Then, with a saved
`map_layout.json` in the prop folder:

```bash
python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 --png          # -> map.png
python3 diagrams/scripts/proof_map.py --prop Book2/Prop02 --all_layouts  # one PNG per map_layout*.json
```

`--scale N` (default 2) and `--transparent` are also accepted.
