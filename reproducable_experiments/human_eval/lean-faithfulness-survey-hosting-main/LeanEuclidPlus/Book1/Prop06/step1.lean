import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s1 (a b c : Point) (hne : |(a─b)| ≠ |(a─c)|) :
    |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)| := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inr h
  · exact Or.inl h

end Elements.Book1
