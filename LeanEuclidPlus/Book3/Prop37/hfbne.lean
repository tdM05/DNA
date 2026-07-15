import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_37_hfbne (f b : Point) (ABC : Circle)
    (h1 : f.isCentre ABC) (h2 : b.onCircle ABC) : f ≠ b := by euclid_finish

end Elements.Book3
