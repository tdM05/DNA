import SystemE
import Book1.Prop45.step20_fkss
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20 (f g h k l m : Point) (FG KH FK LM HM GH : Line)
    (hf_FG : f.onLine FG)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hh_GH : h.onLine GH)
    (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hGHLM : ¬GH.intersectsLine LM)
    (hFGKH : ¬FG.intersectsLine KH)
    (step17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG) :
    formParallelogram f l k m FG KH FK LM := by
  have step20_fkss : f.sameSide k LM := by euclid_apply (helper_1_45_step20_fkss f h k l m FK LM KH HM GH (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)) (by euclid_assumption "" (show |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM); assumption)))
  euclid_finish

end Elements.Book1
