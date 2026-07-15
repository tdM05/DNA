import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_hEF_int_BCD (e : Point) (BCD : Circle) (EF : Line)
    (hcen : e.isCentre BCD) (he_on : e.onLine EF) :
    EF.intersectsCircle BCD := by
  exact intersection_circle_line_2 e BCD EF ⟨center_inside_circle e BCD hcen, he_on⟩

end Elements.Book3
