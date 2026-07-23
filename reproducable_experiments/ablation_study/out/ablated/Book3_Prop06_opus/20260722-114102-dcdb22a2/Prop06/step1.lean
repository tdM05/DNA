import SystemE

namespace Elements.Book3

theorem helper_3_6_step1 (f : Point) (ABC CDE : Circle)
    (h1 : f.isCentre ABC) (h2 : f.isCentre CDE) :
    f.isCentre ABC ∧ f.isCentre CDE := by
  euclid_finish

end Elements.Book3
