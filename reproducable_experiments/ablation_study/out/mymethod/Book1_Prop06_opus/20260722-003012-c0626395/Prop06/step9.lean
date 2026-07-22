import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step9
  (a b c d : Point) (AB BC AC DC : Line)
  (haAB : a.onLine AB) (hbAB : b.onLine AB)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hdDC : d.onLine DC) (hcDC : c.onLine DC)
  (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hab : a ≠ b)
  (hbet : between b d a)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (hstep8 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a))
  : False := by
  obtain ⟨h8a, h8b, h8c⟩ := hstep8
  euclid_finish

end Elements.Book1
