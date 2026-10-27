import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3


theorem proposition_26 : ∀ (a b c d e f g h : Point) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ c.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧ f.onCircle DEF ∧
  g.isCentre ABC ∧ h.isCentre DEF ∧
  |(g─b)| = |(h─e)| ∧
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
  ∠ b:a:c = ∠ e:d:f →
  ∠ b:g:c = ∠ e:h:f := by
  sorry

end Elements.Book3
