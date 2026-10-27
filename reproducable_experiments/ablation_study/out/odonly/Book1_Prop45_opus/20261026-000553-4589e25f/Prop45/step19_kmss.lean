import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19_kmss (g h k m : Point) (KH HM FG GH : Line)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hg_FG : g.onLine FG)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hk_off : ¬k.onLine GH)
    (hFGKH : ¬FG.intersectsLine KH) :
    k.sameSide m FG := by
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  have hFGKH_ne : FG ≠ KH := by euclid_finish
  have hk_offFG : ¬k.onLine FG := by euclid_finish
  have hm_offFG : ¬m.onLine FG := by euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing k m FG KH)
  euclid_finish

end Elements.Book1
