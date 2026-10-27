import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5_ss (a b c d e h : Point) (AH BG AB CD CH : Line)
    (left_1 : a.onLine AH) (left_2 : d.onLine AH)
    (left_11p : e.onLine AH) (left_12 : h.onLine AH)
    (left_3 : b.onLine BG) (left_4 : c.onLine BG)
    (left_5 : a.onLine AB) (left_6 : b.onLine AB)
    (left_8p : d.onLine CD) (left_9 : c.onLine CD) (right_9 : d ≠ c)
    (left_8 : a.sameSide b CD) (left_10 : ¬AH.intersectsLine BG) (right_10 : ¬AB.intersectsLine CD)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (left_21 : between a d h) (right_21 : between a e h) :
    e.sameSide b CH := by
  euclid_finish

end Elements.Book1
