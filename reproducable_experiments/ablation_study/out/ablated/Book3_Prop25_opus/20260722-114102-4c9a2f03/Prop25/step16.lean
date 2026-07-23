import SystemE

namespace Elements.Book3

theorem helper_3_25_step16 (a b c e : Point) (α₁ : Circle)
    (h1 : e.isCentre α₁) (h2 : a.onCircle α₁)
    (h3 : |(a─e)| = |(e─b)|) (h4 : |(e─b)| = |(e─c)|) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  euclid_finish

end Elements.Book3
