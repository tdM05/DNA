import SystemE

namespace Elements.Book2

theorem proposition_2 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ c.onLine AB ∧ between a c b →
  |(a─b)| * |(b─c)| + |(b─a)| * |(a─c)| = |(a─b)| * |(a─b)| :=
by
  euclid_intros
  have hsum : |(a─c)| + |(c─b)| = |(a─b)| := by euclid_finish
  have hbc : |(b─c)| = |(c─b)| := by euclid_finish
  have hba : |(b─a)| = |(a─b)| := by euclid_finish
  rw [hbc, hba]
  have : |(a─b)| = |(a─c)| + |(c─b)| := hsum.symm
  rw [this]; ring

end Elements.Book2
