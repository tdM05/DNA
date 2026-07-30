import SystemE

namespace Elements.Book2

theorem proposition_8 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  4 * (|(a─b)| * |(b─c)|) + |(a─c)| * |(a─c)| =
    (|(a─b)| + |(b─c)|) * (|(a─b)| + |(b─c)|) :=
by
  euclid_intros
  have hab : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  have hbc : |(b─c)| = |(c─b)| := by euclid_finish
  rw [hab, hbc]; ring

end Elements.Book2
