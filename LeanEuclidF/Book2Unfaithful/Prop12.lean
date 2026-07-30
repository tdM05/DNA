import SystemE
import Book1.Prop47.Main

namespace Elements.Book2

open Elements.Book1

theorem proposition_12 : ∀ (a b c d : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA ∧ (∠ b:a:c : ℝ) > ∟ ∧
  d.onLine CA ∧ between d a c ∧ (∠ b:d:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| =
    |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) :=
by
  euclid_intros
  euclid_apply (line_from_points b d) as BD
  euclid_apply (proposition_47 d b c BD BC CA)
  euclid_apply (proposition_47 d b a BD AB CA)
  have h1 : |(b─c)| * |(b─c)| = |(b─d)| * |(b─d)| + |(d─c)| * |(d─c)| := by euclid_finish
  have h2 : |(b─a)| * |(b─a)| = |(b─d)| * |(b─d)| + |(d─a)| * |(d─a)| := by euclid_finish
  have hdc : |(d─c)| = |(d─a)| + |(a─c)| := by euclid_finish
  have hda : |(d─a)| = |(a─d)| := by euclid_finish
  have hac : |(a─c)| = |(c─a)| := by euclid_finish
  rw [h1, h2, hdc, hda, hac]; ring

end Elements.Book2
