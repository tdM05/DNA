import SystemE
import Book1.Prop30.Main
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17 (f g h k l m : Point) (FG KH FK GH LM HM : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hfk_ss : f.sameSide k GH)
    (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM)
    (hk_off : ¬k.onLine GH) (hm_off : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hFGKH : ¬FG.intersectsLine KH)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))   -- "$FK$ is equal and parallel to $HG$"
  (hassump2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))   -- "$HG$ to $ML$"
  : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  -- $FK$ equal and parallel to $HG$ [Prop.~1.34]:
  euclid_apply (line_from_points g k) as GK
  euclid_apply (proposition_34 f g k h FG KH FK GH GK)
  -- $KF$ also equal and parallel to $ML$ [Prop.~1.30]:
  have hGHFK : GH ≠ FK := by euclid_finish
  have hLMGH : LM ≠ GH := by euclid_finish
  have hFKLM : FK ≠ LM := by euclid_finish
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1
