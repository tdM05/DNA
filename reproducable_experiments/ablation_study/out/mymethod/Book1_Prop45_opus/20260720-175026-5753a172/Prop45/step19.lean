import SystemE
import Book1.Prop33.Main
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step19
  (f g h k l m : Point) (FK LM FG KH GH GL : Line)
  (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
  (hl_LM : l.onLine LM) (hm_LM : m.onLine LM) (hml : m ≠ l)
  (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
  (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hh_KH : h.onLine KH) (hgh : g ≠ h)
  (hfk_ss : f.sameSide k GH) (hl_GL : l.onLine GL)
  (hFGKH : ¬FG.intersectsLine KH) (step16 : FG = GL)
  (step17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
  (step18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG) :
  |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  have hl_FG : l.onLine FG := by rw [step16]; exact hl_GL
  have hne : FG ≠ KH := by euclid_finish
  have hfl : f.sameSide l KH := sameSide_of_parallel_both f l FG KH hf_FG hl_FG hne hFGKH
  euclid_apply (proposition_33 f k l m FK LM FG KH)
  euclid_finish

end Elements.Book1
