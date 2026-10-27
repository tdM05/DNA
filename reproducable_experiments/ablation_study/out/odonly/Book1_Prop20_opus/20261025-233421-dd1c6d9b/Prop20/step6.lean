import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6
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
    (step1 : between b a d)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ b:c:d > ∠ b:d:c)   -- "$DCB$ is a triangle having the angle $BCD$ greater than $BDC$"
    : |(d─b)| > |(b─c)| := by
  euclid_apply (proposition_19 b c d BC DC AB)
  euclid_finish

end Elements.Book1
