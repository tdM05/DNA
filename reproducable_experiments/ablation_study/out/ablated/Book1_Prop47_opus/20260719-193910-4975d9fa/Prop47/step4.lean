import SystemE

namespace Elements.Book1

theorem helper_1_47_step4 (a b c g : Point) (AB : Line)
    (h1 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟))
    (h2 : ¬(g.onLine AB)) (h3 : ¬(c.onLine AB)) (h4 : ¬(g.sameSide c AB)) :
    c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟) := by
  euclid_finish

end Elements.Book1
