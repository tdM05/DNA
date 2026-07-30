# Faithfulness Evaluation Rubric for Euclidean Lean Formalizations

## Purpose

This rubric evaluates how faithfully a Lean formalization represents the mathematical content of a textbook proposition and proof. The textbook is the reference standard. Reviewers should not evaluate general elegance, maintainability, proof brevity, annotation quality, or code style except insofar as these affect mathematical faithfulness to the textbook.

Each metric is scored independently on a 0-5 scale. Do not aggregate scores unless a separate protocol specifies how to do so.

## Reviewer Protocol

Reviewers should compare three objects:

1. The textbook proposition and proof.
2. The Lean theorem statement.
3. The mathematical content of the Lean proof, including invoked lemmas, constructions, and automation outcomes when those are needed to understand the proof.

Reviewers should ignore comments, sentence IDs, natural-language annotations, and metadata unless they help locate the corresponding mathematical content. A formalization should not receive credit merely because a comment claims faithfulness; the mathematical statement and proof must substantiate it.

If a proof uses automation, reviewers should evaluate the mathematical facts established by that automation where recoverable from the proof state, helper lemmas, generated subgoals, imported theorem statements, or build artifacts. If the mathematical content of an automated step cannot be recovered well enough to judge faithfulness, assign the score warranted by the recoverable evidence.

When the Lean formalization makes implicit textbook reasoning explicit, do not penalize it solely for being more explicit. Penalize only when the added material changes the mathematical claim, changes the argument, introduces unjustified assumptions, or uses dependencies that are not faithful to the textbook's reasoning.

## Metric 1: Object Correspondence

Are the textbook's mathematical objects represented by the correct Lean objects with the same roles?

Focus on points, lines, segments, angles, figures, constructed objects, incidences, betweenness relations, equality relations, and role assignments.

Score guide:

- **0 - Object mapping invalid.** The main objects are mapped incorrectly, making the formalization about different geometric entities than the textbook.
- **1 - Major object-role errors.** Several important objects or roles are confused, omitted, or swapped in ways that materially change the proposition or proof.
- **2 - Partial object correspondence.** The principal objects are identifiable, but important constructed objects, incidences, angle vertices, side correspondences, or role assignments are wrong or ambiguous.
- **3 - Mostly correct object correspondence with notable issues.** Most objects are mapped correctly, but there are nontrivial local mismatches, such as an incorrect orientation, a missing constructed object, or a questionable side/angle correspondence.
- **4 - Faithful object correspondence with minor formal differences.** All central objects and roles match the textbook. Minor discrepancies are limited to harmless naming, orientation conventions, or formal encodings that preserve the mathematical content.
- **5 - Fully faithful object correspondence.** Every relevant textbook object, including constructed objects and their roles, is represented by the corresponding Lean object or relation with no substantive mismatch.

Common failure modes:

- Treating a line as a segment, or a segment as an unrestricted line.
- Reversing an angle in a way that changes its vertex or rays.
- Constructing a point with the right name but wrong betweenness or incidence relation.
- Mapping the common side or corresponding sides incorrectly in a congruence argument.

## Metric 2: Proof-Step Coverage

Are the textbook's essential mathematical proof steps present in the Lean proof?

Focus on whether the formal proof includes the major mathematical moves of the textbook proof. This metric does not require sentence-by-sentence alignment, but it does require the proof to contain the same essential mathematical content.

Score guide:

- **0 - Textbook proof not represented.** The Lean proof does not contain the textbook's essential proof strategy or steps, even if it proves a related result.
- **1 - Minimal overlap with textbook proof.** Only isolated pieces of the textbook argument appear; most essential proof moves are absent or replaced by unrelated reasoning.
- **2 - Partial step coverage.** Some central proof steps are present, but multiple essential steps are missing, bypassed, or replaced by substantially different mathematical arguments.
- **3 - Mostly covered with significant gaps.** The Lean proof includes the main proof strategy and several essential steps, but one or more important steps are absent, compressed beyond recoverability, or only indirectly represented.
- **4 - Nearly complete step coverage.** All essential textbook steps are present, with only minor omissions or compressions that do not change the mathematical proof strategy.
- **5 - Complete step coverage.** Every essential mathematical step of the textbook proof is represented in the Lean proof, allowing for routine formal elaboration and harmless decomposition into sublemmas.

For a proof by contradiction, the contradiction-producing step counts as an essential proof step. For a construction-based proof, the construction and its required properties count as essential proof steps.

Common failure modes:

- Proving the proposition using a later theorem or a stronger modern theorem instead of the textbook route.
- Skipping a construction that is central to the textbook proof.
- Establishing the final result by automation without recoverable intermediate mathematical content.
- Replacing a geometric argument with an algebraic or analytic argument that is not equivalent to the textbook's proof strategy.

## Metric 3: Proof-Structure Fidelity

Does the Lean proof preserve the textbook's mathematical dependency structure?

Focus on how proof steps depend on one another: contradiction setup, case splits, construction order, use of intermediate facts, and whether later conclusions rely on the same earlier facts as in the textbook. Do not require superficial line order when the mathematical dependencies are unchanged.

Score guide:

- **0 - Incompatible proof structure.** The formal proof follows a fundamentally different dependency structure from the textbook proof.
- **1 - Severe structural mismatch.** The proof contains some textbook-like steps but combines or orders them in a way that changes the argument's mathematical logic.
- **2 - Partial structural fidelity.** The broad strategy is recognizable, but important dependencies, branches, or contradiction structure are missing, reversed, or replaced.
- **3 - Mostly faithful structure with notable deviations.** The proof follows the textbook's main dependency pattern, but one or more significant structural components are altered, hidden, or not justified in the same way.
- **4 - Faithful structure with minor formal differences.** The proof preserves the textbook's dependency structure. Differences are limited to formal necessities, such as making implicit cases explicit or splitting bundled steps into lemmas.
- **5 - Fully faithful structure.** The proof's mathematical dependencies match the textbook argument closely, including construction order, use of intermediate facts, branching, contradiction structure, and final conclusion.

Formal case splits should be scored under this metric. A case split omitted in the textbook may be faithful if it merely completes an implicit textbook argument. It is unfaithful if it changes the proof strategy, assumes an unjustified case, or proves a different branch by unrelated reasoning.

Common failure modes:

- Using the desired conclusion, or an equivalent result, before it is established in the textbook argument.
- Constructing objects in a way that depends on facts not yet available in the textbook proof.
- Handling a formally necessary branch with a different theorem that bypasses the textbook argument.
- Deriving contradiction from an unrelated inconsistency rather than from the textbook's contradiction pattern.

## Metric 4: Cited-Dependency Fidelity

When the textbook cites a proposition, postulate, definition, common notion, or previously established result, does the Lean proof use a corresponding formal dependency or an explicitly equivalent mathematical principle?

Focus on cited mathematical support, not on textual citation markers or comments.

Score guide:

- **0 - Cited dependencies ignored or replaced wholesale.** The formal proof does not use the textbook's cited mathematical dependencies or equivalent principles, and instead relies on unrelated results.
- **1 - Major dependency mismatch.** Most important cited dependencies are absent, replaced by stronger later results, or used in ways that do not correspond to the textbook.
- **2 - Partial dependency fidelity.** Some cited dependencies are represented, but several important ones are missing, mismatched, or replaced by non-equivalent principles.
- **3 - Mostly faithful dependencies with significant caveats.** The main cited dependencies are present, but at least one important dependency is replaced by a stronger or less directly corresponding formal result.
- **4 - Faithful dependencies with minor formal substitutions.** The proof uses formal analogues of the cited dependencies. Any substitutions are mathematically equivalent or are unavoidable due to the formal library's organization.
- **5 - Fully faithful dependencies.** Each cited textbook dependency is represented by a direct formal analogue or a clearly equivalent formal principle used at the corresponding mathematical point in the proof.

When a textbook relies on an uncited standard background principle, score it under Metric 6 unless it functions as a cited dependency in the proof.

Common failure modes:

- Using a theorem that already contains the proposition being proved.
- Replacing a construction postulate with an existence theorem that assumes stronger conditions.
- Using a later proposition where the textbook uses an earlier one.
- Replacing a common notion with an unrelated analytic fact unless the formal proof shows it is serving the same mathematical role.

## Metric 5: Assumption and Side-Condition Fidelity

Are all additional formal assumptions, side conditions, and proof obligations mathematically justified by the textbook setup or standard Euclidean background?

Lean proofs often require explicit facts that the textbook leaves implicit. This metric evaluates whether those requirements are faithful to the textbook setting. Do not penalize a formalization merely because a justified side condition is discharged by automation rather than displayed as a named intermediate fact. Penalize only when the side condition is unjustified, too strong, inconsistent with the textbook configuration, or not recoverable well enough to determine its mathematical status.

Score guide:

- **0 - Unjustified assumptions central to the proof.** The proof relies on assumptions or side conditions that are not in the textbook, not implied by the setup, and materially affect the result.
- **1 - Major assumption problems.** Several important side conditions are unjustified, too strong, or inconsistent with the textbook configuration.
- **2 - Partial assumption fidelity.** Some side conditions are justified, but important assumptions remain unsupported, stronger than what the textbook permits, or mathematically unclear.
- **3 - Mostly justified assumptions with notable concerns.** Most added formal obligations follow from the textbook setup, but at least one nontrivial side condition is unjustified, uncertain, or requires a stronger reading of the textbook than warranted.
- **4 - Faithful assumptions with minor gaps.** Added assumptions and side conditions are justified by the textbook setup or standard Euclidean background. Remaining issues are minor, local, or evidentially uncertain without threatening the proof's mathematical faithfulness.
- **5 - Fully faithful assumptions and side conditions.** Every formal side condition used by the proof is justified by the textbook statement, the constructed configuration, prior established facts, or accepted Euclidean background principles. This score is compatible with automation when the automated obligations are mathematically justified.

Examples of side conditions to check:

- Distinctness of points.
- Non-collinearity or nondegeneracy of triangles.
- Incidence of points on lines.
- Betweenness and orientation of constructed points.
- Positivity or nonzero length/area facts.
- Existence conditions for constructed objects.
- Conditions required by congruence, intersection, or area lemmas.

Common failure modes:

- Assuming a point lies between two others when the construction only gives collinearity.
- Assuming nondegeneracy without deriving it from the triangle hypothesis.
- Using a construction theorem outside its valid hypotheses.
- Relying on an orientation or side-of-line condition not implied by the textbook diagram or proof.

## Scoring Notes

Assign the score that best matches the evidence. Do not average across subissues within a metric mechanically. A single severe faithfulness error can cap the score for that metric even if other aspects are strong.

Use the full scale. A score of 5 should be reserved for cases where the formalization is faithful up to routine formal encoding. A score of 3 should indicate a recognizably faithful formalization with meaningful issues. A score of 0 or 1 should indicate that the metric is substantially failed.

When uncertain between two adjacent scores, choose the lower score if the uncertainty concerns a central mathematical point, and the higher score if the uncertainty concerns only a peripheral or recoverable detail.

Reviewers should provide brief justification for each metric score, citing the relevant Lean theorem, helper lemma, or proof fragment when possible.
