import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step5 (a b c d d' : Point) (AB BC AC DC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_dpAB : d'.onLine AB) (h_add' : between a d d')
    (h_dDC : d.onLine DC) (h_cDC : c.onLine DC)
    (h_step1 : between b a d) (h_step4 : ∠ a:d:c = ∠ a:c:d) :
    ∠ b:c:d > ∠ a:d:c := by
  euclid_finish

end Elements.Book1
