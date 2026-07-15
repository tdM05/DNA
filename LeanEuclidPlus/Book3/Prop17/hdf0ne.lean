import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_17_hdf0ne (d f0 : Point) (AE : Line)
    (hd_on : d.onLine AE) (hf0_off : ¬f0.onLine AE) : d ≠ f0 := by
  intro h
  exact hf0_off (h ▸ hd_on)

end Elements.Book3
