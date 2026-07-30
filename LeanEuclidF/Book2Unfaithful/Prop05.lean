import SystemE

namespace Elements.Book2

theorem proposition_5 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c d ∧ between c d b ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(d─b)| + |(c─d)| * |(c─d)| = |(c─b)| * |(c─b)| :=
by
  euclid_intros
  have had : |(a─d)| = |(c─b)| + |(c─d)| := by euclid_finish
  have hdb : |(c─d)| + |(d─b)| = |(c─b)| := by euclid_finish
  have hdb' : |(d─b)| = |(c─b)| - |(c─d)| := by rw [← hdb]; ring
  rw [had, hdb']; ring

end Elements.Book2
