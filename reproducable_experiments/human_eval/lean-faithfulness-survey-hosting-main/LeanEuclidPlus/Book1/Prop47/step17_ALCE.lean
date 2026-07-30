import SystemE
import Book1.Prop30.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s17_x1
    (a b c : Point) (AL CE BD BC : Line)
    (ha_AL : a.onLine AL) (hoffBD : ¬a.onLine BD) (h_offCE : ¬a.onLine CE)
    (hb_BD : b.onLine BD) (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_CE : c.onLine CE) (h_c_nBD : ¬c.onLine BD)
    (h_nALBD : ¬AL.intersectsLine BD) (h_nBDCE : ¬BD.intersectsLine CE) :
    ¬AL.intersectsLine CE := by
  euclid_apply (proposition_30 AL CE BD)
  euclid_finish

end Elements.Book1
