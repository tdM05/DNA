import SystemE
import Book1.Prop30.Main
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17
  (f g h k l m : Point) (FG KH FK GH HM GL LM : Line)
  (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
  (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
  (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
  (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
  (hfk_GH : f.sameSide k GH)
  (hFGKH : ¬FG.intersectsLine KH) (hFKGH : ¬FK.intersectsLine GH)
  (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
  (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
  (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l)
  (hhg_LM : h.sameSide g LM)
  (hHMGL : ¬HM.intersectsLine GL) (hGHLM : ¬GH.intersectsLine LM)
  (hm_offGH : ¬m.onLine GH) (hk_offGH : ¬k.onLine GH)
  (hmk_ss : ¬m.sameSide k GH)
  (step10 : KH = HM)
  (hassump1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
  (hassump2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
  : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  -- [Prop.~1.34]: FK equal & parallel to HG (re-established here so the citation lives in this cone)
  euclid_apply (line_from_points g k) as GK
  euclid_apply (proposition_34 f g k h FG KH FK GH GK)
  have hm_KH : m.onLine KH := by rw [step10]; exact hm_HM
  have hFKLM : FK ≠ LM := by euclid_finish
  have hLMGH : LM ≠ GH := by euclid_finish
  have hGHFK : GH ≠ FK := by euclid_finish
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1
