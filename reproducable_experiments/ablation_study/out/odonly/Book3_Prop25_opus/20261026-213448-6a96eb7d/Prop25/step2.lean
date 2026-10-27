import SystemE
import Book1.Prop11.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step2 (a b c d : Point) (AC DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c)
    (hbet : between a d c) (hadc : |(a─d)| = |(d─c)|)
    (hab : |(a─b)| = |(c─b)|) (hbAC : ¬b.onLine AC)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) :
    ∠ a:d:b = ∟ := by
  euclid_apply (Elements.Book1.proposition_11 a c d AC)
  euclid_finish

end Elements.Book3
