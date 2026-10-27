import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10_form (a b c d3 d3' : Point) (AB BC AC D3A : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB)
    (h_d3pBC : d3'.onLine BC) (h_bcd3' : between b c d3') (h_cd3d3' : between c d3 d3')
    (h_d3D3A : d3.onLine D3A) (h_aD3A : a.onLine D3A) :
    formTriangle b a d3 AB D3A BC := by
  euclid_finish

end Elements.Book1
