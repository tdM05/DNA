import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_hefne (e f : Point) (AFG : Circle)
    (hcen : e.isCentre AFG) (hf_on : f.onCircle AFG) : e ≠ f := by
  have he_in : e.insideCircle AFG := center_inside_circle e AFG hcen
  euclid_finish

end Elements.Book3
