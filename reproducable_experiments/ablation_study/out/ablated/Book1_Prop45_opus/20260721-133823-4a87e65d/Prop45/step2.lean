import SystemE

namespace Elements.Book1

theorem helper_1_45_step2 (a b d e₁ e₂ e₃ f g h k : Point) (FG KH FK GH : Line)
    (h1 : f.onLine FG) (h2 : g.onLine FG) (h3 : k.onLine KH) (h4 : h.onLine KH)
    (h5 : f.onLine FK) (h6 : k.onLine FK) (h7 : g.onLine GH) (h8 : h.onLine GH)
    (h9 : g ≠ h) (h10 : f.sameSide k GH) (h11 : ¬(FG.intersectsLine KH)) (h12 : ¬(FK.intersectsLine GH))
    (h13 : ∠ h:k:f = ∠ e₁:e₂:e₃)
    (h14 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) :
    formParallelogram f g k h FG KH FK GH ∧ (∠ h:k:f = ∠ e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) := by
  euclid_finish

end Elements.Book1
