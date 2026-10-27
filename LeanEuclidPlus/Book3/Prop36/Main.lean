import SystemE

namespace Elements.Book3


theorem proposition_36 : ∀ (a b c d : Point) (ABC : Circle) (DB : Line),
    a.onCircle ABC ∧ c.onCircle ABC ∧ d.outsideCircle ABC ∧
    between d c a ∧
    d.onLine DB ∧ b.onLine DB ∧ b.onCircle ABC ∧ ¬ DB.intersectsCircle ABC →
    |(d─a)| * |(d─c)| = |(d─b)| * |(d─b)| := by
  sorry

end Elements.Book3
