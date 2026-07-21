import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step16
  (b c d e₁ e₂ e₃ f g h k l m : Point) (FG GL GH HM LM : Line)
  (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
  (hg_FG : g.onLine FG) (hf_FG : f.onLine FG)
  (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
  (hfk_ss : f.sameSide k GH) (hmk_ss : ¬m.sameSide k GH)
  (hk_off : ¬k.onLine GH) (hm_off : ¬m.onLine GH)
  (step3 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c))
  (step15 : ∠ h:g:f + ∠ h:g:l = ∟ + ∟) :
  FG = GL := by
  euclid_apply (proposition_14 h g f l GH FG GL)
  euclid_finish

end Elements.Book1
