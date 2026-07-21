import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step1 (b a d d' : Point) (AB : Line)
    (hb : b.onLine AB) (ha : a.onLine AB) (hd' : d'.onLine AB)
    (h1 : between b a d') (h2 : between a d d') : between b a d := by
  euclid_finish

end Elements.Book1
