import SystemE
import Book3.Prop09.Main

namespace Elements.Book3

open Elements.Book1

-- A circle drawn with center E and radius EA passes through B and C as well [Prop.~3.9]: since
-- EA = EB = EC and A is on the circle α₁ centered at E, the equal radii place B and C on α₁ too,
-- and E is its center. (Prop. III.9 is the converse fact that such an E is the unique center.)
theorem helper_3_25_step16 (a b c e : Point) (α₁ : Circle) (AB DB AG EC AC : Line)
    (h1 : |(a─e)| = |(e─b)|) (h2 : |(e─b)| = |(e─c)|)
    (h3 : e.isCentre α₁) (h4 : a.onCircle α₁)
    (h5 : a.onLine AB) (h6 : b.onLine AB)
    (h7 : e.onLine DB) (h8 : b.onLine DB)
    (h9 : a.onLine AG) (h10 : e.onLine AG)
    (h11 : e.onLine EC) (h12 : c.onLine EC)
    (h13 : a.onLine AC) (h14 : c.onLine AC) (h15 : ¬b.onLine AC) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  have hb : b.onCircle α₁ := by
    euclid_apply (point_on_circle_if e a b α₁)
    euclid_finish
  have hc : c.onCircle α₁ := by
    euclid_apply (point_on_circle_if e a c α₁)
    euclid_finish
  euclid_apply (proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
