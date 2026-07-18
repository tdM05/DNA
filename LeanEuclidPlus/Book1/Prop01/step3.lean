import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_1_step3 (a b c : Point) (AB CA CB : Line) (BCD ACE : Circle)
    (hab : a ≠ b)
    (ha_centre : a.isCentre BCD) (hc_bcd : c.onCircle BCD)
    (hb_centre : b.isCentre ACE) (hc_ace : c.onCircle ACE)
    (hc_ca : c.onLine CA) (ha_ca : a.onLine CA)
    (hc_cb : c.onLine CB) (hb_cb : b.onLine CB) :
    distinctPointsOnLine c a CA ∧ distinctPointsOnLine c b CB := by
  euclid_finish

end Elements.Book1
