# Faithfulness Evaluation Rubric for Euclidean Lean Formalizations

## Purpose

This rubric evaluates how faithfully a Lean formalization represents the mathematical content of a textbook proposition and proof. The textbook is the reference standard. Reviewers should focus on the mathematical statement and proof content, not comments, metadata, or annotation labels.

Each formalization is scored independently on the metric below. The later preference questions compare the two formalizations directly.

## Reviewer Protocol

Reviewers should compare three objects:

1. The textbook proposition and proof.
2. The Lean theorem statement.
3. The mathematical content of the Lean proof, including invoked lemmas, constructions, and automation outcomes when those are needed to understand the proof.

If a proof uses automation, evaluate the mathematical facts established by that automation where recoverable from the proof state, helper lemmas, generated subgoals, imported theorem statements, or build artifacts.

When the Lean formalization makes implicit textbook reasoning explicit, do not penalize it solely for being more explicit. Penalize only when the added material changes the mathematical claim, changes the argument, introduces unjustified assumptions, or bypasses essential textbook reasoning.

## Metric 1: Step Fidelity

How faithfully does the Lean formalization make the textbook's mathematical route recoverable through its stated mathematical steps and dependencies?

Focus on whether the formalization captures the essential objects, constructions, dependencies, and conclusions of the textbook proof, with enough mathematical evidence to recover the route. It need not match sentence-by-sentence, but it should preserve the mathematical route and make important steps recoverable.

Score guide:

- **0 - Not represented.** The Lean proof does not represent the textbook proof's mathematical content, even if it proves a related result.
- **1 - Minimal fidelity.** Only isolated textbook-like facts appear; the proof mostly follows a different or unrecoverable route.
- **2 - Partial fidelity.** Some essential steps are present, but several important objects, constructions, dependencies, or conclusions are missing, changed, or too hidden to judge confidently.
- **3 - Mostly faithful with gaps.** The main textbook route is recognizable, but some essential objects, dependencies, conclusions, ordering relationships, or automated steps are not stated with enough evidence to recover their role in the textbook argument.
- **4 - Faithful with minor issues.** The essential textbook steps and dependencies are represented in an order that preserves the textbook route, with only minor formal differences or peripheral details that do not prevent recovery of that route.
- **5 - Fully faithful and transparent.** The formalization closely preserves the textbook's mathematical route, including essential objects, constructions, dependencies, and conclusions, with the key mathematical steps recoverable.

## Scoring Notes

Assign the score that best matches the evidence. Use the full scale. A score of 5 should be reserved for cases where the formalization is faithful up to routine formal encoding. A score of 3 should indicate a recognizably faithful formalization with meaningful issues.

When uncertain between two adjacent scores, choose the lower score if the uncertainty concerns a central mathematical point, and the higher score if the uncertainty concerns only a peripheral or recoverable detail.
