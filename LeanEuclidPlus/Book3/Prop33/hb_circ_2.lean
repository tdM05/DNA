import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN

namespace Elements.Book3

-- b is on circle α (centre f, radius fa): since f is the midpoint, |(f─b)| = |(f─a)| = radius.
set_option systemE.solverTime 30 in
theorem helper_3_33_hb_circ_2
    (a b f : Point) (α : Circle)
    (hfcen : f.isCentre α) (hacirc : a.onCircle α) (haffb : |(a─f)| = |(f─b)|) :
    b.onCircle α := by
  euclid_finish

end Elements.Book3
