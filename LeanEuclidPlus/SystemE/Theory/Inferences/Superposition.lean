import SystemE.Theory.Sorts
import SystemE.Theory.Relations

/--
A combination of the two superposition rules in [Avigad et al., 2009]
-/
axiom superposition : ∀ (a b c d g h : Point) (AB BC AC L : Line),
  formTriangle a b c AB BC AC ∧ distinctPointsOnLine d g L ∧ ¬(h.onLine L) →
  ∃ (b' c' : Point) (BC' AC' : Line), (∠ b:a:c : ℝ) = (∠ b':d:c') ∧ (∠ a:c:b : ℝ) = (∠ d:c':b') ∧ (∠ c:b:a : ℝ) = (∠ c':b':d) ∧
  |(a─b)| = |(d─b')| ∧ |(b─c)| = |(b'─c')| ∧ |(c─a)| = |(c'─d)| ∧ b'.onLine L ∧ ¬(between b' d g) ∧ c'.sameSide h L ∧ distinctPointsOnLine b' c' BC' ∧ distinctPointsOnLine d c' AC'

/--
Superposition for a SEGMENT of a circle (the circle analogue of `superposition`, used by III.24).
-/
axiom segment_superposition : ∀ (a e b c d h : Point) (AB CD : Line) (AEB : Circle),
  formCircularSegment a e b AB AEB ∧
  distinctPointsOnLine c d CD ∧ ¬(h.onLine CD) ∧
  |(a─b)| = |(c─d)| →
  ∃ (a' e' b' : Point) (AEB' : Circle),
    a' = c ∧ b'.onLine CD ∧ ¬(between b' c d) ∧ e'.sameSide h CD ∧
    |(a─b)| = |(a'─b')| ∧ (∠ a':e':b' : ℝ) = (∠ a:e:b) ∧
    (⌓ a':e':b' : ℝ) = (⌓ a:e:b) ∧
    formCircularSegment a' e' b' CD AEB'
