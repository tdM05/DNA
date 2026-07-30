import SystemE

namespace Elements.Book2

theorem proposition_9 : ∀ (a b c d : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ d.onLine AB ∧
  between a c b ∧ |(a─c)| = |(c─b)| ∧ between c d b →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) :=
by
  euclid_intros
  have hac : |(a─c)| = |(c─d)| + |(d─b)| := by euclid_finish
  have had : |(a─d)| = |(a─c)| + |(c─d)| := by euclid_finish
  rw [had, hac]; ring

end Elements.Book2
