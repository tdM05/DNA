import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19_ksm (f g h k m : Point) (FG KH HM GH : Line)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
  (hniFGKH : ¬FG.intersectsLine KH)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
  (hsame : f.sameSide k GH)
  : k.sameSide m FG := by
  have hfgkh : FG ≠ KH := by euclid_finish
  have hkFG : ¬k.onLine FG := by euclid_finish
  have hmFG : ¬m.onLine FG := by euclid_finish
  euclid_finish

end Elements.Book1
