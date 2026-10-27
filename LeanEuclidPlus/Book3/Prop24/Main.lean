import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_24 : ∀ (a e b f : Point) (AB : Line) (AEB CFD : Circle),
  a.onCircle AEB ∧ e.onCircle AEB ∧ b.onCircle AEB ∧
  a.onCircle CFD ∧ f.onCircle CFD ∧ b.onCircle CFD ∧
  distinctPointsOnLine a b AB ∧
  ¬ e.onLine AB ∧ ¬ f.onLine AB ∧
  e.sameSide f AB ∧
  ∠ a:e:b = ∠ a:f:b →
  AEB = CFD := by
  sorry

end Elements.Book3
