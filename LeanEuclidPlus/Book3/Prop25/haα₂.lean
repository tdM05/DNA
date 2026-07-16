import SystemE


namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_haα₂ (a : Point) (α₂ : Circle)
    (ha_circ : a.onCircle α₂) :
    a.onCircle α₂ := by
  exact ha_circ

end Elements.Book3
