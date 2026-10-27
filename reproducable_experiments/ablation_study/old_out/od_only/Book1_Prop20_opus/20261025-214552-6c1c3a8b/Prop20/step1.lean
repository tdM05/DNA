import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step1 (a b d d' : Point) (AB : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_dpAB : d'.onLine AB)
    (h_bad' : between b a d') (h_add' : between a d d') :
    between b a d := by
  euclid_finish

end Elements.Book1
