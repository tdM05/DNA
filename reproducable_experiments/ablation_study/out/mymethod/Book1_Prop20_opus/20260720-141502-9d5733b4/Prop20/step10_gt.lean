import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10_gt (a b c f f' : Point) (AB BC AC FA : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hf'_BC : f'.onLine BC) (h_bcf' : between b c f') (h_cff' : between c f f')
    (hf_FA : f.onLine FA) (ha_FA : a.onLine FA)
    (hstep10_iso : ∠ c:f:a = ∠ c:a:f) :
    ∠ b:a:f > ∠ c:f:a := by
  have hsame1 : b.sameSide c FA := by euclid_finish
  have hsame2 : f.sameSide c AB := by euclid_finish
  euclid_apply (sum_angles_onlyif a b f c AB FA)
  euclid_finish

end Elements.Book1
