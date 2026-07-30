import SystemE

namespace Elements.Book2

theorem proposition_4 : ∀ (a b c : Point) (AB : Line),
  distinctPointsOnLine a b AB ∧ between a c b →
  |(a─b)| * |(a─b)| =
    |(a─c)| * |(a─c)| + |(c─b)| * |(c─b)| + 2 * (|(a─c)| * |(c─b)|) :=
by
  euclid_intros
  have hsum : |(a─b)| = |(a─c)| + |(c─b)| := by euclid_finish
  rw [hsum]; ring

end Elements.Book2
