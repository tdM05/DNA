import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_4_s8_x1
  (a b c d e f : Point) (b' c' : Point)
  (ptImg : Point → Point)
  (h_ptImg_a : ptImg a = d)
  (s1 : ptImg b = e)
  (s3 : ptImg c = f)
  : ptImg a = d ∧ ptImg b = e ∧ ptImg c = f :=
  ⟨h_ptImg_a, s1, s3⟩

end Elements.Book1
