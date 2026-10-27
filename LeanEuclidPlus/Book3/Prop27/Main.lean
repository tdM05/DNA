import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_27 : ∀ (a b c d e f g h : Point) (BC EF : Line) (ABC DEF : Circle),
  g.isCentre ABC ∧ h.isCentre DEF ∧
  b.onCircle ABC ∧ c.onCircle ABC ∧ e.onCircle DEF ∧ f.onCircle DEF ∧
  a.onCircle ABC ∧ d.onCircle DEF ∧
  distinctPointsOnLine b c BC ∧ distinctPointsOnLine e f EF ∧
  a ≠ b ∧ a ≠ c ∧ d ≠ e ∧ d ≠ f ∧
  a.sameSide g BC ∧ d.sameSide h EF ∧
  |(g─b)| = |(h─e)| ∧
  ∠ b:g:c = ∠ e:h:f →
  ∠ b:a:c = ∠ e:d:f := by
  sorry

end Elements.Book3
