import SystemE


namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_hbα₂ (a b d : Point) (α₂ : Circle)
    (hcentre : d.isCentre α₂) (ha_circ : a.onCircle α₂)
    (hrad : |(d─a)| = |(d─b)|) :
    b.onCircle α₂ := by
  euclid_finish

end Elements.Book3
