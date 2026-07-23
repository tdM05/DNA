import SystemE

namespace Elements.Book3

theorem helper_3_36_step26 (b c e : Point) (ABC : Circle)
    (h1 : e.isCentre ABC) (h2 : c.onCircle ABC) (h3 : b.onCircle ABC) :
    |(e─c)| = |(e─b)| := by
  euclid_finish

end Elements.Book3
