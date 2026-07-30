import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_6_s2 (a b c : Point) (hgt : |(a─b)| > |(a─c)|) :
    |(a─b)| > |(a─c)| := by
  exact hgt

end Elements.Book1
