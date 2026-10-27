import SystemE

namespace Elements.Book1

theorem helper_44_between_hal :
    ∀ (a b e g f h k l m : Point) (AB FG BG EF AH HB KL : Line),
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    between a b e ∧
    g.onLine FG ∧ f.onLine FG ∧
    b.onLine AB ∧ e.onLine AB ∧
    g.onLine BG ∧ b.onLine BG ∧
    f.onLine EF ∧ e.onLine EF ∧
    g.sameSide b EF ∧
    f ≠ e ∧
    ¬FG.intersectsLine AB ∧
    ¬BG.intersectsLine EF ∧
    a.onLine AH ∧
    ¬AH.intersectsLine BG ∧
    ¬AH.intersectsLine EF ∧
    h.onLine AH ∧ h.onLine FG ∧
    h.onLine HB ∧ b.onLine HB ∧
    k.onLine HB ∧ k.onLine EF ∧
    k.onLine KL ∧
    ¬KL.intersectsLine AB ∧
    ¬KL.intersectsLine FG ∧
    l.onLine AH ∧ l.onLine KL ∧
    m.onLine BG ∧ m.onLine KL →
    between h a l := by
  sorry

theorem helper_44_between_gbm :
    ∀ (a b e g f h k l m : Point) (AB FG BG EF AH HB KL : Line),
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    between a b e ∧
    g.onLine FG ∧ f.onLine FG ∧
    b.onLine AB ∧ e.onLine AB ∧
    g.onLine BG ∧ b.onLine BG ∧
    f.onLine EF ∧ e.onLine EF ∧
    g.sameSide b EF ∧
    f ≠ e ∧
    ¬FG.intersectsLine AB ∧
    ¬BG.intersectsLine EF ∧
    a.onLine AH ∧
    ¬AH.intersectsLine BG ∧
    ¬AH.intersectsLine EF ∧
    h.onLine AH ∧ h.onLine FG ∧
    h.onLine HB ∧ b.onLine HB ∧
    k.onLine HB ∧ k.onLine EF ∧
    k.onLine KL ∧
    ¬KL.intersectsLine AB ∧
    ¬KL.intersectsLine FG ∧
    l.onLine AH ∧ l.onLine KL ∧
    m.onLine BG ∧ m.onLine KL →
    between g b m := by
  sorry

theorem proposition_44' : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ x : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), Point.opposingSides m x AB ∧ formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m) + (Triangle.area △ a:l:m) = (Triangle.area △ c₁:c₂:c₃) := by
  sorry

end Elements.Book1
