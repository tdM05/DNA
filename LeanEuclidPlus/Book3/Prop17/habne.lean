import SystemE

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_habne (a b : Point) (BCD : Circle)
    (ha_not_on : ¬a.onCircle BCD)
    (hb_onBCD : b.onCircle BCD) :
    a ≠ b := by
  euclid_finish

end Elements.Book3
