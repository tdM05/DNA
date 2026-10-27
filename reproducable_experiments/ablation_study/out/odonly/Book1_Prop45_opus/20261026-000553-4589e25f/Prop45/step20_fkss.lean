import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20_fkss (f h k l m : Point) (FK LM KH HM GH : Line)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hh_GH : h.onLine GH)
    (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hGHLM : ¬GH.intersectsLine LM)
    (step17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM)) :
    f.sameSide k LM := by
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  have hk_offLM : ¬k.onLine LM := by euclid_finish
  have hf_offLM : ¬f.onLine LM := by euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing f k LM FK)
  euclid_finish

end Elements.Book1
