import SystemE

namespace Elements.Book1

theorem helper_1_12_step2 (c d : Point) (EFG : Circle)
    (h1 : c.isCentre EFG) (h2 : d.onCircle EFG) :
    c.isCentre EFG ∧ d.onCircle EFG := by
  euclid_finish

end Elements.Book1
