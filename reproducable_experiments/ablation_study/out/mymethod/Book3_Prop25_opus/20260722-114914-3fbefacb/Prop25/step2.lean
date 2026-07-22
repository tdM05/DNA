import SystemE
import Book1.Prop11.Main
import Book1.Prop08.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step2 (a b c d : Point) (AC AB DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (habcb : |(a─b)| = |(c─b)|)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) :
    ∠ a:d:b = ∟ := by
  euclid_apply (proposition_11 a c d AC)
  euclid_apply (line_from_points c b) as CB
  euclid_apply (proposition_8 d a b d c b AC AB DB AC CB DB)
  euclid_finish

end Elements.Book3
