import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_bkhm (g h k m : Point) (KH HM GH : Line)
  (hopp : k.opposingSides m GH) (hhGH : h.onLine GH)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH)
  (hmHM : m.onLine HM) (hstep10 : KH = HM)
  : between k h m := by euclid_finish

end Elements.Book1
