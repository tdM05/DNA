import SystemE
import Book1.Prop11.Main
import Book1.Prop08.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step2 (a b c d : Point) (AC DB AB : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC) (hac : a ≠ c)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c) (hmid : |(a─d)| = |(d─c)|)
    (heq : |(a─b)| = |(c─b)|)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB) :
    ∠ a:d:b = ∟ := by
  -- Euclid's construction: erect the perpendicular at D [Prop.~1.11].
  euclid_apply (proposition_11 a c d AC) as f
  -- The pre-given B is equidistant from A, C, and D is the midpoint, so triangles
  -- D-A-B and D-C-B are congruent (SSS) ⟹ the adjacent angles at D are equal.
  euclid_apply (line_from_points c b) as CB
  euclid_apply (proposition_8 d a b d c b AC AB DB AC CB DB)
  -- equal adjacent angles on the straight line AC ⟹ each is a right angle.
  euclid_finish

end Elements.Book3
