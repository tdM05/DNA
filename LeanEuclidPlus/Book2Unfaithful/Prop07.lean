import SystemE

namespace Elements.Book2

theorem proposition_7 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| + |(b─c)| * |(b─c)| =
    2 * (|(a─b)| * |(b─c)|) + |(c─a)| * |(c─a)| :=
by
  euclid_intros
  have hsum : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  have hca : |(c─a)| = |(a─c)| := by euclid_finish
  have hbc : |(b─c)| = |(c─b)| := by euclid_finish
  rw [hsum, hca, hbc]; ring

end Elements.Book2
