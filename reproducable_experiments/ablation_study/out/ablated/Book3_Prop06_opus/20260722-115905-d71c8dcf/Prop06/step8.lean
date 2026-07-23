import SystemE

namespace Elements.Book3

theorem helper_3_6_step8 (ABC CDE : Circle)
    (h1 : ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE)) :
    ¬(∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE) := h1

end Elements.Book3
