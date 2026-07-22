import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_6_step9
  (a b c d : Point) (AB BC AC DC : Line)
  (hang : ∠ a:b:c = ∠ a:c:b)
  (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
  (hbBC : b.onLine BC) (hcBC : c.onLine BC)
  (hcAC : c.onLine AC) (haAC : a.onLine AC)
  (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
  (hbet : between b d a)
  (hdDC : d.onLine DC) (hcDC : c.onLine DC)
  (hstep8 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a)) :
    False := by
  obtain ⟨hdc, hbdc, hbcd⟩ := hstep8
  euclid_finish

end Elements.Book1
