# Prop47 (Pythagoras) — Phase B proving notes

Status: ALL 21 sentences + construction lemmas certified via --subtree. --check + --dependency clean (78 nodes). --all running, then wire_main (Phase C).

## ⚠ CRITICAL: proposition_41 / proposition_4 ARGUMENT ORDER
proposition_41 a b c d e AE BC AB CD BE CE — the parallelogram is `formParallelogram a d b c AE BC AB CD`
and the conclusion is `△a:b:c + △a:c:d = 2·△e:b:c`. Pick the arg order so `formParallelogram a d b c ...`
matches your proven parallelogram VERBATIM (vertex order matters!). For step14 the square GAFB with
conclusion △g:f:b+△g:b:a=2△c:f:b needs `proposition_41 g f b a c AC BF GF AB FC BC` (NOT g a f b c —
that makes the precondition `formParallelogram g b a f` which mismatches `g a f b` and euclid_apply
SEARCHES ENDLESSLY → 45s timeout that LOOKS like a load-timeout at "[786/787] Replayed Prop41" but is
actually the apply). Convert the two triangulations with `parallelogram_area` (SystemE, no Prop41 import)
then euclid_finish. This unblocked step14 after a very long dead-end chase.

## step17 = full MIRROR of steps 8-16 for the AC-leg
"the parallelogram CL = square HC" is proven "similarly" — it needs the whole ∠ECA=∠KCB (mirror of
step8 windmill, ~40 nodes) + SAS + area-congruence + proposition_41×2 + doubles, all with b↔c, AB↔AC,
GB↔HC, d↔e, f↔k, g↔h, BD↔CE, BF↔CK etc. Reuse the step8/11-16 patterns (foot on AL for the c-inside
facts is SHARED since AL⊥BC is the same; the crux (D)-analogs use the AC∩(square-side) two-right-angles
trick). Big but mechanical given the templates below.

## steps 18-21 (light, area algebra):
- 18 (BDEC = BL+CL = GB+HC): sum_areas / the m,l split + step16 + step17.
- 19 (BDEC=|bc|²): rectangle_area on the square BDEC (right angles).
- 20 (GB=|ba|², HC=|ac|²): rectangle_area on each square.
- 21 (final): linarith over 18,19,20.

## Hard-won techniques (reuse for step17, which mirrors step13/14):

- **step8 (∠DBA=∠FBC, the crux):** sum_angles_onlyif on both additions needs 4 sameSide
  facts (A,B,C,D). (A)/(B) reduce to the altitude-foot fact `¬b.sameSide c AL` (step8_bcAL):
  construct m=AL∩BC, prove `between b m c` via proposition_17 (acute base angles rule out
  the foot being outside), then pasch_3. (B) then via a∈AL∥BD, transversal DE (`between d l e`),
  e~c seed. (A) via triple_incidence_2 from (B)+¬d.sameSide a BC. (C)/(D): the foot doesn't
  help (m~c wrt BF). (D) c.sameSide a BF: direct — if BF separated a,c, the crossing p=AC∩BF
  gives triangle pab TWO right angles (∠pab=∟ from p on AC, ∠abp=∟ from p on BF) ⟹ prop17 contra.
  (C) via triple_incidence_2 from (D)+hfcAB.
- **¬f.onLine BC / off-line "second right angle" facts:** two-right-angles + prop17 (step11_foffBC).
  Reused across step11,12,14.
- **proposition_41 (area doubling, steps 13/14/17):** apply IN THE CONTAINER (needs loose incidence
  atoms in context to discharge formParallelogram fast; an ISOLATED leaf with only the packaged
  formParallelogram hyp makes euclid_apply SMT-search and time out). formParallelogram + formTriangle
  as sub-nodes. Do the triangulation conversion (△g:f:b+△g:b:a ↔ △a:g:f+△a:f:b) via a SEPARATE
  SystemE-only sub-node calling `parallelogram_area` (avoids re-loading Prop41's heavy closure).
- Object binders MUST all be at the FRONT of a helper signature (Point/Line grouped), else the
  Main-wire passes hypotheses as objects → type mismatch.
- Many distinctness/off-line facts (b≠c, b≠d, ¬d.onLine AB, BC≠DE, ...) are NOT literal in Main;
  derive them in-body from the square lengths (|c-e|=|b-c|, e≠c) / angles (∠b:d:e=∟) / hoffBD.
