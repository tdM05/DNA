import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step2
    (a b d e₁ e₂ e₃ f g k h : Point) (FG KH FK GH : Line)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH) (hgh : g ≠ h)
    (hfk_GH : f.sameSide k GH)
    (hFGKH : ¬FG.intersectsLine KH) (hFKGH : ¬FK.intersectsLine GH)
    (hangle : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (harea : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) :
    formParallelogram f g k h FG KH FK GH ∧ (∠ h:k:f = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) := by
  euclid_finish

end Elements.Book1
