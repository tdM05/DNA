import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (FG KH HM GL GH LM : Line)
    (hstep10 : KH = HM) (hstep16 : FG = GL)
    (hk_KH : k.onLine KH) (hm_HM : m.onLine HM)
    (hf_FG : f.onLine FG) (hl_GL : l.onLine GL)
    (hss : f.sameSide k GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hGHLM : ¬(GH.intersectsLine LM))
    (hk_notGH : ¬(k.onLine GH)) (hm_notGH : ¬(m.onLine GH)) (hmk_ss : ¬(m.sameSide k GH)) :
    distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  euclid_finish

end Elements.Book1
