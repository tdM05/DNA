import SystemE
import Book1.Prop45.step21_bkhm
import Book1.Prop45.step21_bfgl
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point) (FG KH FK LM GL GH HM : Line)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hm_HM : m.onLine HM) (step10 : KH = HM)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hl_GL : l.onLine GL) (step16 : FG = GL)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
    (hfk_ss : f.sameSide k GH)
    (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH) (hmk_ns : ¬m.sameSide k GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hGHLM : ¬GH.intersectsLine LM)
    (step20 : formParallelogram f l k m FG KH FK LM)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)   -- "triangle $ABD$ is equal to parallelogram $FH$"
  (hassump2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)   -- "$DBC$ to $GM$"
  : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  have step21_bkhm : between k h m := by euclid_apply (helper_1_45_step21_bkhm h k m KH HM GH (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.sameSide k GH; assumption)))
  have step21_bfgl : between f g l := by euclid_apply (helper_1_45_step21_bfgl f g k l m FG GL GH LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show FG = GL; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.sameSide k GH; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
