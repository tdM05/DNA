import SystemE

namespace Elements.Book2

theorem proposition_10 : ∀ (a b c d : Point) (AD : Line),
  distinctPointsOnLine a d AD ∧ c.onLine AD ∧ b.onLine AD ∧
  between a c b ∧ between a b d ∧ |(a─c)| = |(c─b)| →
  |(a─d)| * |(a─d)| + |(d─b)| * |(d─b)| =
    2 * (|(a─c)| * |(a─c)| + |(c─d)| * |(c─d)|) :=
by
  euclid_intros
  have h1 : |(a─d)| = |(a─c)| + |(c─d)| := by euclid_finish
  have h2 : |(c─d)| = |(c─b)| + |(b─d)| := by euclid_finish
  have h3 : |(a─c)| = |(c─b)| := by euclid_finish
  have h4 : |(d─b)| = |(b─d)| := by euclid_finish
  rw [h1, h2, h4, h3]; ring

end Elements.Book2
