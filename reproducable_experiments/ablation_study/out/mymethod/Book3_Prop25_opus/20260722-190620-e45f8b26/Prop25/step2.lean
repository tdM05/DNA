import SystemE
import Book1.Prop11.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step2 (a b c d : Point) (AC DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hlen : |(a─b)| = |(c─b)|) (hbtw : between a d c) (hmid : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) :
    ∠ a:d:b = ∟ := by
  euclid_apply (proposition_11 a c d AC)
  euclid_finish

end Elements.Book3
