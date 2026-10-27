import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10_bet (b c d3 d3' : Point) (BC : Line)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC) (h_d3pBC : d3'.onLine BC)
    (h_bcd3' : between b c d3') (h_cd3d3' : between c d3 d3') :
    between b c d3 := by
  euclid_finish

end Elements.Book1
