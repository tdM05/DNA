import SystemE

namespace Elements.Book3

-- EC is equal to EB: both C and B are on the circle and E is its centre, so they are radii.
theorem helper_3_36_step26 (b c e : Point) (ABC : Circle)
    (h1 : e.isCentre ABC) (h2 : c.onCircle ABC) (h3 : b.onCircle ABC) :
    |(e─c)| = |(e─b)| := by
  euclid_finish

end Elements.Book3
