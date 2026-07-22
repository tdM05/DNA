import SystemE
import Book1.Prop06.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step19 (a b c d : Point) (AC AB DB : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboffAC : ¬b.onLine AC)
  (hadc : between a d c)
  (haAB : a.onLine AB) (hbAB : b.onLine AB)
  (hdDB : d.onLine DB) (hbDB : b.onLine DB)
  (hassump1 : ∠ a:b:d = ∠ b:a:d)
  (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)
  : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  obtain ⟨h1, h2⟩ := hassump2
  -- isoceles converse: △dab has equal base angles ∠dab = ∠dba, so |da| = |db|  [Prop.~1.6]
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
