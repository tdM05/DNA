import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step4
    (a b c d d' : Point)
    (AB BC AC DC : Line)
    (ha_AB : a.onLine AB)
    (hb_AB : b.onLine AB)
    (hab : a ≠ b)
    (hbBC : b.onLine BC)
    (hcBC : c.onLine BC)
    (hcAC : c.onLine AC)
    (haAC : a.onLine AC)
    (hABBC : AB ≠ BC)
    (hBCAC : BC ≠ AC)
    (hACAB : AC ≠ AB)
    (hd'_AB : d'.onLine AB)
    (hadd' : between a d d')
    (hdDC : d.onLine DC)
    (hcDC : c.onLine DC)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(d─a)| = |(a─c)|)   -- "$DA$ is equal to $AC$"
    : ∠ a:d:c = ∠ a:c:d := by
  euclid_apply (extend_point AC a c) as e2
  euclid_apply (proposition_5 a d c d' e2 AB DC AC)
  euclid_finish

end Elements.Book1
