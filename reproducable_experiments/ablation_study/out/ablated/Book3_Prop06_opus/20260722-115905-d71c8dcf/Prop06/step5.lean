import SystemE

namespace Elements.Book3

theorem helper_3_6_step5 (f c e : Point) (CDE : Circle)
    (h1 : f.isCentre CDE) (h2 : c.onCircle CDE) (h3 : e.onCircle CDE) :
    |(f─c)| = |(f─e)| := by
  euclid_finish

end Elements.Book3
