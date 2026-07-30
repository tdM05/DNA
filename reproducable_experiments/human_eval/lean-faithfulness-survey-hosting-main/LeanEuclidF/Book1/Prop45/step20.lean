import SystemE
import Helpers.SameSide
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_45_s20
    (f g k h m l : Point) (FG GL GH KH HM FK LM : Line)
    (hf_FG : f.onLine FG)
    (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH)
    (hm_HM : m.onLine HM)
    (hf_FK : f.onLine FK)
    (hk_FK : k.onLine FK)
    (hl_GL : l.onLine GL)
    (hl_LM : l.onLine LM)
    (hm_LM : m.onLine LM)
    (hml : m ≠ l)
    (hh_sg_LM : h.sameSide g LM)
    (s10 : KH = HM)
    (s11_a1 : ¬FG.intersectsLine KH)
    (s16 : FG = GL)
    (s17 : |(k─f)| = |(m─l)| ∧ ¬FK.intersectsLine LM)
    (s18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG) :
    formParallelogram f l k m FG KH FK LM := by
  have hl_FG : l.onLine FG := s16 ▸ hl_GL
  have hm_KH : m.onLine KH := s10 ▸ hm_HM
  have hfl : f ≠ l := s18.2.2.2
  have hg_not_LM : ¬g.onLine LM :=
    same_side_not_on_line g h LM (same_side_symm h g LM hh_sg_LM)
  have hf_not_LM : ¬f.onLine LM := by
    intro hf_LM
    have hFG_LM := two_points_determine_line f l FG LM
      ⟨s18.2, hf_LM, hl_LM⟩
    exact hg_not_LM (hFG_LM ▸ hg_FG)
  have hfk_ss_LM : f.sameSide k LM :=
    sameSide_of_parallel' f k f FK LM hf_FK hk_FK hf_FK hf_not_LM s17.2
  exact ⟨hf_FG, hl_FG, hk_KH, hm_KH, hf_FK, hk_FK,
         ⟨hl_LM, hm_LM, hml.symm⟩, hfk_ss_LM,
         s11_a1, s17.2⟩

end Elements.Book1
