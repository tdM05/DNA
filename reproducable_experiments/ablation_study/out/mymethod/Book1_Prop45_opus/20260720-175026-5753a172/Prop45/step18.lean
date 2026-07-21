import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step18
  (b c d e₁ e₂ e₃ f g h k l m : Point) (KH HM FG GL GH LM : Line)
  (hk_KH : k.onLine KH) (hm_HM : m.onLine HM)
  (hf_FG : f.onLine FG) (hl_GL : l.onLine GL)
  (hfk_ss : f.sameSide k GH) (hmk_ss : ¬m.sameSide k GH)
  (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH)
  (step10 : KH = HM) (step16 : FG = GL)
  (step3 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)) :
  distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG := by
  euclid_finish

end Elements.Book1
