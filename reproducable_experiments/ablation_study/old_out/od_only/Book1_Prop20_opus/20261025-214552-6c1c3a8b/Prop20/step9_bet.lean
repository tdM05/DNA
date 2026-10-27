import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_bet (a b d2 d2' : Point) (AB : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_d2pAB : d2'.onLine AB)
    (h_abd2' : between a b d2') (h_bd2d2' : between b d2 d2') :
    between a b d2 := by
  euclid_finish

end Elements.Book1
