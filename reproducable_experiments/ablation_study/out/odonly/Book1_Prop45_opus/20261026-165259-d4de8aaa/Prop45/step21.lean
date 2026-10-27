import SystemE
import Book1.Prop45.step21_folg
import Book1.Prop45.step21_bfgl
import Book1.Prop45.step21_bkhm
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point) (FG KH HM FK LM GL GH : Line)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)   -- "triangle $ABD$ is equal to parallelogram $FH$"
  (hassump2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)   -- "$DBC$ to $GM$"
  (hstep20 : formParallelogram f l k m FG KH FK LM)
  (hfFG : f.onLine FG) (hgFG : g.onLine FG)
  (hlGL : l.onLine GL) (hstep16 : FG = GL)
  (hkKH : k.onLine KH) (hhKH : h.onLine KH) (hmHM : m.onLine HM) (hstep10 : KH = HM)
  (hgGH : g.onLine GH) (hhGH : h.onLine GH)
  (hlLM : l.onLine LM) (hmLM : m.onLine LM) (hniLMGH : ¬GH.intersectsLine LM)
  (hsame : f.sameSide k GH) (hsameLM : h.sameSide g LM)
  (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  obtain ⟨hopp, _⟩ := hstep9
  have step21_folg : f.opposingSides l GH := by euclid_apply (helper_1_45_step21_folg f g h k l m GH LM (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show k.opposingSides m GH; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)))
  have step21_bfgl : between f g l := by euclid_apply (helper_1_45_step21_bfgl f g l FG GL GH (by euclid_assumption "" (show f.opposingSides l GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show FG = GL; assumption)))
  have step21_bkhm : between k h m := by euclid_apply (helper_1_45_step21_bkhm g h k m KH HM GH (by euclid_assumption "" (show k.opposingSides m GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)))
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
