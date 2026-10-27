import SystemE

namespace Elements.Book1

theorem proposition_42' : ∀ (a b c d₁ d₂ d₃ e : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ between b e c ∧ (|(b─e)| = |(e─c)|) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g : Point) (FG EF CG : Line), a.sameSide f BC ∧ formParallelogram f g e c FG BC EF CG ∧
  (∠ c:e:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c : ℝ) + (Triangle.area △ f:c:g) = (Triangle.area △ a:b:c) := by
  sorry

theorem proposition_42'' : ∀ (a b c d₁ d₂ d₃ h i : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) := by
  sorry

theorem proposition_42''' : ∀ (a b c d₁ d₂ d₃ h i x : Point) (AB BC AC D₁₂ D₂₃ HI : Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ ¬(x.onLine HI) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ ∧ distinctPointsOnLine h i HI →
  ∃ (f g j : Point) (FG FI GJ : Line), f.sameSide x HI ∧ between h i j ∧ formParallelogram f g i j FG HI FI GJ ∧
  (∠ j:i:f : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:i:j : ℝ) + (Triangle.area △ f:j:g) = (Triangle.area △ a:b:c) := by
  sorry

end Elements.Book1
