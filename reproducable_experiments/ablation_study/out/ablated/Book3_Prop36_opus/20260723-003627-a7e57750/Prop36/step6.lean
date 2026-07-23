import SystemE

namespace Elements.Book3

theorem helper_3_36_step6 (b c f : Point) (ABC : Circle)
    (h1 : f.isCentre ABC) (h2 : c.onCircle ABC) (h3 : b.onCircle ABC) :
    |(f─c)| = |(f─b)| := by
  euclid_finish

end Elements.Book3
