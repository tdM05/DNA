import SystemE


namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_haα₃ (a : Point) (α₃ : Circle)
    (ha_circ : a.onCircle α₃) :
    a.onCircle α₃ := by
  exact ha_circ

end Elements.Book3
