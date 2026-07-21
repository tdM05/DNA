import SystemE

namespace Elements.Book1

theorem helper_1_12_step1 (c d : Point) (AB : Line)
    (h1 : ¬(d.onLine AB)) (h2 : ¬(c.onLine AB)) (h3 : ¬(d.sameSide c AB)) :
    d.opposingSides c AB := by
  euclid_finish

end Elements.Book1
