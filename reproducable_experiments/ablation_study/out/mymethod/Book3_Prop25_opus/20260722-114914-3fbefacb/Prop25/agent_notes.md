# Prop25 (Book 3) — Phase B notes

Prop III.25: complete the circle from a given segment. Chord AC, arc apex B (|AB|=|CB|), D=midpoint AC,
DB ⊥ AC. Three cases on ∠ABD vs ∠BAD (>, =, <).

## Key prop signatures (Book1 geometry)
- `Elements.Book1.proposition_10 a b AB : distinctPointsOnLine a b AB → ∃ d, between a d b ∧ |ad|=|db|`
  (construction; in Main `proposition_10 a c AC as d`). satisfies step1 [1.10] construction arm.
- `proposition_11 a b c AB : distinctPointsOnLine a b AB ∧ between a c b → ∃ f, ¬f.onLine AB ∧ ∠ a:c:f = ∟`
  (perpendicular from midpoint). step2 cites [1.11] — NOT a construction here (DB = line_from_points d b),
  so proof arm: must euclid_apply proposition_11 in step2 cone.
- `proposition_6 a b c AB BC AC : formTriangle a b c .. ∧ ∠ a:b:c = ∠ a:c:b → |ab|=|ac|` (isosceles).
  step9 |eb|=|ea| [1.6]; step19 [1.6].
- `proposition_4 a b c d e f .. : formTriangle abc ∧ formTriangle def ∧ |ab|=|de| ∧ |ac|=|df| ∧ ∠bac=∠edf
  → |bc|=|ef| ∧ ∠abc=∠def ∧ ∠acb=∠dfe` (SAS). step12 |ae|=|ce| [1.4].
- `proposition_23' a b c d e x AB CD CE : distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE ∧
  ¬x.onLine AB → ∃ f, f≠a ∧ (f.onLine AB ∨ f.sameSide x AB) ∧ ∠ f:a:b = ∠ d:c:e` (construction, done in Main).
- `Elements.Book3.proposition_9 ABC a b c d : d.insideCircle ABC ∧ a,b,c onCircle ∧ distinct ∧ |da|=|db| ∧
  |db|=|dc| → d.isCentre ABC`. step16 cites [3.9].

## Progress
- Added set_option to Main. Main elaborates (--provable OK).
- (fill in as nodes complete)
