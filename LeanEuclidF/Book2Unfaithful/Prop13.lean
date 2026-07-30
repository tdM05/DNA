import SystemE
import Book1.Prop47.Main

namespace Elements.Book2

open Elements.Book1

theorem proposition_13 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧
  (∠ a:b:c : ℝ) < ∟ ∧ (∠ b:c:a : ℝ) < ∟ ∧ (∠ c:a:b : ℝ) < ∟ ∧
  d.onLine BC ∧ between b d c ∧ (∠ a:d:c : ℝ) = ∟ →
  |(a─c)| * |(a─c)| + 2 * (|(c─b)| * |(b─d)|) =
    |(c─b)| * |(c─b)| + |(b─a)| * |(b─a)| :=
by
  euclid_intros
  euclid_apply (line_from_points d a) as DA
  have hadb : (∠ a:d:b : ℝ) = ∟ := by euclid_finish
  euclid_apply (proposition_47 d a c DA CA BC)
  have hac : |(a─c)| * |(a─c)| = |(a─d)| * |(a─d)| + |(c─d)| * |(c─d)| := by euclid_finish
  euclid_apply (proposition_47 d a b DA AB BC)
  have hba : |(b─a)| * |(b─a)| = |(a─d)| * |(a─d)| + |(b─d)| * |(b─d)| := by euclid_finish
  have hcb : |(c─b)| = |(c─d)| + |(b─d)| := by euclid_finish
  rw [hac, hba, hcb]; ring

end Elements.Book2
