import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21_bfgl (f g k l m : Point) (FG GL GH LM : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hl_GL : l.onLine GL) (step16 : FG = GL)
    (hg_GH : g.onLine GH)
    (hfk_ss : f.sameSide k GH)
    (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hGHLM : ¬GH.intersectsLine LM) :
    between f g l := by
  have hlFG : l.onLine FG := by rw [step16]; exact hl_GL
  have hfl_opp : f.opposingSides l GH := by euclid_finish
  euclid_apply (between_points f g l FG)
  euclid_finish

end Elements.Book1
