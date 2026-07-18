import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step6_opp
    (b h : Point) (AC : Line)
    (hhb : ¬h.sameSide b AC) (hboffAC : ¬b.onLine AC) (hhoffAC : ¬h.onLine AC) :
    b.opposingSides h AC := by
  euclid_finish

end Elements.Book1
