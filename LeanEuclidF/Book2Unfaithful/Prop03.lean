import SystemE

namespace Elements.Book2

theorem proposition_3 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(b─c)| = |(a─c)| * |(c─b)| + |(b─c)| * |(b─c)| :=
by
  euclid_intros
  have hsum : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  have hsym : |(c─b)| = |(b─c)| := by euclid_finish
  rw [hsum, hsym]; ring

end Elements.Book2
