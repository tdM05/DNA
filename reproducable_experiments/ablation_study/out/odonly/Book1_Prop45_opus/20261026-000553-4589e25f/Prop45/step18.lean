import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18 (f g h k l m : Point) (KH HM FG GL GH LM : Line)
    (hk_KH : k.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hf_FG : f.onLine FG) (hl_GL : l.onLine GL) (step16 : FG = GL)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
    (hfk_ss : f.sameSide k GH)
    (hk_off : ¬k.onLine GH) (hm_off : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hGHLM : ¬GH.intersectsLine LM) :
    distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  have hmKH : m.onLine KH := by rw [step10]; exact hm_HM
  have hlFG : l.onLine FG := by rw [step16]; exact hl_GL
  have hfl_opp : f.opposingSides l GH := by euclid_finish
  euclid_finish

end Elements.Book1
