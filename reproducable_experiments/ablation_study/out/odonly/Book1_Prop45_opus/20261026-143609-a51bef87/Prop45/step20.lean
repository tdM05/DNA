import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20 (f k l m : Point) (FG KH FK LM GH : Line)
    (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hf_FG : f.onLine FG) (hk_KH : k.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml_ne : m ≠ l)
    (hk_notGH : ¬(k.onLine GH)) (hm_notGH : ¬(m.onLine GH)) (hmk_ss : ¬(m.sameSide k GH))
    (hGHLM : ¬(GH.intersectsLine LM))
    (hni_FGKH : ¬(FG.intersectsLine KH)) :
    formParallelogram f l k m FG KH FK LM := by
  obtain ⟨hd_km, hd_fl⟩ := hstep18
  obtain ⟨hlen, hFKLM⟩ := hstep17
  have hk_nLM : ¬k.onLine LM := by euclid_finish
  have hf_nLM : ¬f.onLine LM := by euclid_finish
  have hfk_LM : f.sameSide k LM := by euclid_finish
  euclid_finish

end Elements.Book1
