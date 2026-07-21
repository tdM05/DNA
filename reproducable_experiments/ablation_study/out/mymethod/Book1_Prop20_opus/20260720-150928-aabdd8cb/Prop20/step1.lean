import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step1 (a b d d' : Point) (AB : Line)
    (ha : a.onLine AB) (hb : b.onLine AB) (hd' : d'.onLine AB) (hab : a ≠ b)
    (h1 : between b a d') (h2 : between a d d') : between b a d := by
  euclid_finish

end Elements.Book1
