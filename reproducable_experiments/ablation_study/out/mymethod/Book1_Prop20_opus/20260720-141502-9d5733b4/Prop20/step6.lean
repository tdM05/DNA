import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6 (a b c d d' : Point) (AB BC AC DC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hd'_AB : d'.onLine AB) (h_add' : between a d d')
    (hd_DC : d.onLine DC) (hc_DC : c.onLine DC)
    (hstep1 : between b a d)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ b:c:d > ∠ b:d:c)   -- "$DCB$ is a triangle having the angle $BCD$ greater than $BDC$"
    : |(d─b)| > |(b─c)| := by
  have hd_AB : d.onLine AB := by euclid_finish
  have hcAB : ¬ c.onLine AB := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hbc : b ≠ c := by euclid_finish
  have hBCDC : BC ≠ DC := by euclid_finish
  have hDCAB : DC ≠ AB := by euclid_finish
  have hangle : ∠ b:c:d > ∠ c:d:b := by euclid_finish
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
