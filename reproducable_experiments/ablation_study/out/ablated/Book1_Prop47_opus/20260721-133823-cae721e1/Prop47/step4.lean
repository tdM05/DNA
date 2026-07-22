import SystemE

namespace Elements.Book1

theorem helper_1_47_step4 (a b c g : Point) (AB : Line)
    (h1 : ¬(g.onLine AB)) (h2 : ¬(c.onLine AB)) (h3 : ¬(g.sameSide c AB))
    (h4 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟)) :
    c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟) := by
  euclid_finish

end Elements.Book1
