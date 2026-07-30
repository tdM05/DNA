import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x15
    (a b c e : Point) (CE BC AC : Line)
    (hc_CE : c.onLine CE) (hc_BC : c.onLine BC) (hc_AC : c.onLine AC)
    (he_CE : e.onLine CE) (hb_BC : b.onLine BC) (ha_AC : a.onLine AC)
    (hce : c ≠ e)
    (h_a_nBC : ¬a.onLine BC)
    (h_ne_same_a_BC : ¬e.sameSide a BC)
    (h_aSameB_CE : a.sameSide b CE) :
    e.sameSide b AC := by
  euclid_apply (triple_incidence_2 CE BC AC c e b a)
  euclid_finish

end Elements.Book1
