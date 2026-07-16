import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_5_hEFG_int_ABC (ABC : Circle) (EFG : Line) (e : Point)
    (he_inside_ABC : e.insideCircle ABC) (heEFG : e.onLine EFG)
    : EFG.intersectsCircle ABC := by
  exact intersection_circle_line_2 e ABC EFG ⟨he_inside_ABC, heEFG⟩

end Elements.Book3
