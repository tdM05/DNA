import SystemE

namespace Elements.Book3

theorem helper_3_11_step9 (f g a : Point)
    (h1 : ¬(¬(between f g a))) :
    between f g a := by
  by_contra hn
  exact h1 hn

end Elements.Book3
