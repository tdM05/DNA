import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step2 (a b d e₁ e₂ e₃ f g k h : Point) (FG KH FK GH : Line)
    (hfFG : f.onLine FG) (hgFG : g.onLine FG) (hkKH : k.onLine KH) (hhKH : h.onLine KH)
    (hfFK : f.onLine FK) (hkFK : k.onLine FK) (hgGH : g.onLine GH) (hhGH : h.onLine GH)
    (hss : f.sameSide k GH) (hgh : g ≠ h)
    (hpar1 : ¬FG.intersectsLine KH) (hpar2 : ¬FK.intersectsLine GH)
    (hang : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (harea : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) :
    formParallelogram f g k h FG KH FK GH ∧ (∠ h:k:f = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) := by
  euclid_finish

end Elements.Book1
