import SystemE

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_9_hfa (a f : Point) (AF : Line)
    (h : distinctPointsOnLine a f AF) : f ≠ a :=
  fun heq => h.2.2 heq.symm

end Elements.Book1
