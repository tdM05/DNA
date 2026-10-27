import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem proposition_29 : ∀ (b c e f k l : Point) (ABC DEF : Circle),
  k.isCentre ABC ∧ l.isCentre DEF ∧
  b.onCircle ABC ∧ c.onCircle ABC ∧
  e.onCircle DEF ∧ f.onCircle DEF ∧
  |(k─b)| = |(l─e)| ∧
  ∠ b:k:c = ∠ e:l:f →
  |(b─c)| = |(e─f)| := by
  sorry

end Elements.Book3
