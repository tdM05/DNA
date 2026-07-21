import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20
  (f g h k l m : Point) (FG KH FK LM GH HM GL : Line)
  (hf_FG : f.onLine FG) (hf_FK : f.onLine FK) (hk_FK : k.onLine FK) (hk_KH : k.onLine KH)
  (hl_GL : l.onLine GL) (hm_HM : m.onLine HM)
  (hl_LM : l.onLine LM) (hm_LM : m.onLine LM) (hml : m ≠ l)
  (hFGKH : ¬FG.intersectsLine KH) (hFKGH : ¬FK.intersectsLine GH)
  (hmk_ss : ¬m.sameSide k GH) (hm_offGH : ¬m.onLine GH) (hk_offGH : ¬k.onLine GH)
  (step10 : KH = HM) (step16 : FG = GL)
  (step17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM)) :
  formParallelogram f l k m FG KH FK LM := by
  have hl_FG : l.onLine FG := by rw [step16]; exact hl_GL
  have hm_KH : m.onLine KH := by rw [step10]; exact hm_HM
  have hne : FK ≠ LM := by euclid_finish
  have hfk_LM : f.sameSide k LM := sameSide_of_parallel_both f k FK LM hf_FK hk_FK hne step17.2
  euclid_finish

end Elements.Book1
