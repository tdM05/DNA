import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_bkhm (h k m : Point) (KH HM GH : Line)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hh_GH : h.onLine GH)
    (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH) :
    between k h m := by
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  euclid_apply (between_points k h m KH)
  euclid_finish

end Elements.Book1
