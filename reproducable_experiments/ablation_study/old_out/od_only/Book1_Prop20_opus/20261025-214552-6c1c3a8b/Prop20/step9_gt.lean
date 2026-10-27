import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_gt (a b c d2 d2' : Point) (AB BC AC D2C : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_d2pAB : d2'.onLine AB) (h_bd2d2' : between b d2 d2')
    (h_d2D2C : d2.onLine D2C) (h_cD2C : c.onLine D2C)
    (h_bet : between a b d2) (h_iso : ∠ b:d2:c = ∠ b:c:d2) :
    ∠ a:c:d2 > ∠ a:d2:c := by
  euclid_finish

end Elements.Book1
