import SystemE
import Book1.Prop06.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step19 (a b c d : Point) (AC AB DB : Line)
    (hAC_a : a.onLine AC) (hAC_c : c.onLine AC)
    (hb_off : ¬b.onLine AC)
    (hbet : between a d c)
    (hAB_a : a.onLine AB) (hAB_b : b.onLine AB)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:b:d = ∠ b:a:d)   -- "angle $ABD$ is equal to $BAD$"
  (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)   -- "$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$"
  : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  -- Triangle ABD is isosceles (∠ABD = ∠BAD) ⟹ DA = DB [Prop.~1.6].
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
