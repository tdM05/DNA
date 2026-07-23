import SystemE

namespace Elements.Book3

theorem helper_3_6_step7 (f c b e : Point) (ABC CDE : Circle)
    (h1 : f.isCentre ABC) (h2 : f.isCentre CDE)
    (h3 : c.onCircle ABC) (h4 : c.onCircle CDE)
    (h5 : ABC ≠ CDE) (h6 : |(f─e)| = |(f─b)|) :
    False := by
  euclid_finish

end Elements.Book3
