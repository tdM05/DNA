import SystemE

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step17 (a b c : Point) (α₁ : Circle)
    (h1 : a.onCircle α₁) (h2 : b.onCircle α₁) (h3 : c.onCircle α₁) :
    a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  euclid_finish

end Elements.Book3
