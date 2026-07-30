# RQ1 — Human Evaluation (survey data + hosting app)

The double-blind human study behind **RQ1** (§5): 14 formal-methods reviewers, independent of
the authors, compared anonymized **Pistis** and **LeanEuclid** formalizations of Book I
propositions. Reviewers are identified only by opaque codes (e.g. `R-26WCS8WR`) — no names or
emails appear anywhere.

## Contents

- **`survey-response/`** — the collected responses:
  - `step_responses.csv` — per-step fidelity ratings (`reviewer_code, proposition_id,
    method_id, metric_id, score, …`). 254 ratings.
  - `preference_responses.csv` — pairwise preference judgments (`…, question_id, choice,
    preferred_method_id, …`). 381 judgments.
  - `method_id`: `new_method` = Pistis, `leaneuclid` = the baseline.
- **`lean-faithfulness-survey-hosting-main/`** — the survey web app the reviewers used:
  `LeanEuclidPlus/eval/survey/` holds the server (`server.py`), the web UI (`web/`), the rubric
  and rendered proofs shown to reviewers (`data/survey_data.json`), and the extraction scripts.
  The bundled `LeanEuclid/` and `LeanEuclidPlus/Book*` trees are the exact proof sources the app
  rendered, kept so the survey is self-contained. `deploy/` holds example service configs
  (`*.example` — no real secrets).

These CSVs are the source for the aggregate scores and preference rates reported in RQ1
(`fig-survey-overview`, `fig-survey-prop-collage-split`).
