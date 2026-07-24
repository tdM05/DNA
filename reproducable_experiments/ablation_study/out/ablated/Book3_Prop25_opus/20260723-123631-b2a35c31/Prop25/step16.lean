import SystemE
import Book3.Prop09.Main

namespace Elements.Book3

open Elements.Book1

-- The three radii EA, EB, EC are equal, E is the centre of α₁ and A is on it, so by the
-- transfer of equal radii B and C lie on α₁ as well; [Prop.~3.9] certifies E as the centre.
theorem helper_3_25_step16 (a b c e : Point) (α₁ : Circle) (AC : Line)
    (hcen : e.isCentre α₁) (haon : a.onCircle α₁)
    (hr1 : |(a─e)| = |(e─b)|) (hr2 : |(e─b)| = |(e─c)|)
    (hac1 : a.onLine AC) (hac2 : c.onLine AC)
    (hbAC : ¬b.onLine AC) (hac : a ≠ c) :
    e.isCentre α₁ ∧ a.onCircle α₁ ∧ b.onCircle α₁ ∧ c.onCircle α₁ := by
  have hb : b.onCircle α₁ := by euclid_finish
  have hc : c.onCircle α₁ := by euclid_finish
  euclid_apply (proposition_9 α₁ a b c e)
  euclid_finish

end Elements.Book3
