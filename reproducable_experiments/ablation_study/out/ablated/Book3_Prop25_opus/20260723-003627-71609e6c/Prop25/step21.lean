import SystemE

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step21 (a c d : Point) (α₂ : Circle)
    (h1 : between a d c) (h2 : d.isCentre α₂) :
    between a d c ∧ d.isCentre α₂ := by
  euclid_finish

end Elements.Book3
