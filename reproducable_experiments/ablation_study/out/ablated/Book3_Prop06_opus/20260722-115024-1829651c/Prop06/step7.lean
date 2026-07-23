import SystemE

namespace Elements.Book3

theorem helper_3_6_step7 (f b e : Point) (ABC CDE : Circle)
    (h1 : f.isCentre ABC) (h2 : f.isCentre CDE)
    (h3 : b.onCircle ABC) (h4 : e.onCircle CDE)
    (h5 : |(f─e)| = |(f─b)|) (h6 : ABC ≠ CDE) :
    False := by
  euclid_finish

end Elements.Book3
