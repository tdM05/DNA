import SystemE
import Book1.Prop05.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10_iso (a b c f f' : Point) (AB BC AC FA : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hf'_BC : f'.onLine BC) (h_cff' : between c f f')
    (h_cf_ca : |(c─f)| = |(c─a)|)
    (hf_FA : f.onLine FA) (ha_FA : a.onLine FA) :
    ∠ c:f:a = ∠ c:a:f := by
  euclid_apply (extend_point AC c a) as g2
  euclid_apply (proposition_5 c f a f' g2 BC FA AC)
  euclid_finish

end Elements.Book1
