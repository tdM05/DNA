import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point) (FG KH FK LM GH : Line)
    (hassump1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (hassump2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
    (hstep20 : formParallelogram f l k m FG KH FK LM)
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (hg_FG : g.onLine FG)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hh_KH : h.onLine KH)
    (hk_notGH : ¬(k.onLine GH)) (hm_notGH : ¬(m.onLine GH)) (hmk_ss : ¬(m.sameSide k GH))
    (hf_sk : f.sameSide k GH)
    (hl_LM : l.onLine LM) (hm_LM : m.onLine LM) (hGHLM : ¬(GH.intersectsLine LM)) :
    Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  obtain ⟨⟨hk_KH, hm_KH, _⟩, ⟨hf_FG, hl_FG, _⟩⟩ := hstep18
  have hlsm : l.sameSide m GH := by euclid_finish
  have hbkm : between k h m := by euclid_finish
  have hbfl : between f g l := by euclid_finish
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
