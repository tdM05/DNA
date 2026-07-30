import SystemE

namespace Elements.Book2

theorem proposition_1 : ∀ (a₁ a₂ b c d e : Point) (A BC : Line),
  distinctPointsOnLine a₁ a₂ A ∧ distinctPointsOnLine b c BC ∧
  d.onLine BC ∧ e.onLine BC ∧ between b d e ∧ between d e c →
  |(a₁─a₂)| * |(b─c)| =
    |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| :=
by
  euclid_intros
  have hsum1 : |(b─d)| + |(d─e)| = |(b─e)| := by euclid_finish
  have hsum2 : |(b─e)| + |(e─c)| = |(b─c)| := by euclid_finish
  have hbc : |(b─c)| = |(b─d)| + |(d─e)| + |(e─c)| := by
    calc |(b─c)|
        = |(b─e)| + |(e─c)| := by rw [← hsum2]
      _ = (|(b─d)| + |(d─e)|) + |(e─c)| := by rw [← hsum1]
      _ = |(b─d)| + |(d─e)| + |(e─c)| := by ring
  rw [hbc]; ring

end Elements.Book2
