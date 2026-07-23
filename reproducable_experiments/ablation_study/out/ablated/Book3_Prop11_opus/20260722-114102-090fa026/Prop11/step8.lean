import SystemE

namespace Elements.Book3

theorem helper_3_11_step8 (f g a : Point)
    (h1 : ¬(¬(between f g a))) :
    ¬(¬(between f g a)) := by
  exact h1

end Elements.Book3
