import SystemE

namespace Elements.Book3

theorem helper_3_6_step7 (f e b : Point) (ABC CDE : Circle)
    (h1 : |(f─e)| = |(f─b)|)
    (h2 : f.isCentre CDE) (h3 : f.isCentre ABC)
    (h4 : e.onCircle CDE) (h5 : b.onCircle ABC)
    (h6 : ABC ≠ CDE) :
    False := by
  euclid_finish

end Elements.Book3
