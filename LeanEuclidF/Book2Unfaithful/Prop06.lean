import SystemE

namespace Elements.Book2

theorem proposition_6 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between a b d →
  |(a─d)| * |(d─b)| + |(c─b)| * |(c─b)| = |(c─d)| * |(c─d)| :=
by
  euclid_intros
  have h1 : |(a─d)| = |(a─c)| + |(c─b)| + |(b─d)| := by euclid_finish
  have h2 : |(c─d)| = |(c─b)| + |(b─d)| := by euclid_finish
  have h3 : |(d─b)| = |(b─d)| := by euclid_finish
  rw [h1, h2, h3]
  have hcb : |(a─c)| = |(c─b)| := by euclid_finish
  rw [hcb]; ring

end Elements.Book2
