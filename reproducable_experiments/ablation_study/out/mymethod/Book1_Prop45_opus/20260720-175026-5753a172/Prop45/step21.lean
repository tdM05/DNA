import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21
  (a b c d e₁ e₂ e₃ f g h k l m : Point) (FG KH FK LM GH HM GL : Line)
  (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
  (hk_KH : k.onLine KH) (hh_KH : h.onLine KH) (hl_GL : l.onLine GL) (hm_HM : m.onLine HM)
  (hfk_ss : f.sameSide k GH) (hmk_ss : ¬m.sameSide k GH)
  (hk_offGH : ¬k.onLine GH) (hm_offGH : ¬m.onLine GH)
  (step10 : KH = HM) (step16 : FG = GL)
  (step20 : formParallelogram f l k m FG KH FK LM)
  (step9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
  (step3 : formParallelogram h m g l HM GL GH LM ∧ (∠ g:h:m = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c))
  (hassump1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
  (hassump2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
  : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  have hl_FG : l.onLine FG := by rw [step16]; exact hl_GL
  have hm_KH : m.onLine KH := by rw [step10]; exact hm_HM
  have hlm_ss : l.sameSide m GH := by euclid_finish
  have hfl_opp : f.opposingSides l GH := by euclid_finish
  have hbetFGL : between f g l := by euclid_finish
  have hbetKHM : between k h m := by euclid_finish
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
