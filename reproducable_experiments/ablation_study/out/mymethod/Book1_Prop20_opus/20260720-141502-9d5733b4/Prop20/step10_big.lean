import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10_big (a b c f f' : Point) (AB BC AC FA : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hf'_BC : f'.onLine BC) (h_bcf' : between b c f') (h_cff' : between c f f')
    (hf_FA : f.onLine FA) (ha_FA : a.onLine FA)
    (hstep10_gt : ∠ b:a:f > ∠ c:f:a) :
    |(f─b)| > |(b─a)| := by
  have hf_BC : f.onLine BC := by euclid_finish
  have haBC : ¬ a.onLine BC := by euclid_finish
  have hbf : b ≠ f := by euclid_finish
  have hba : b ≠ a := by euclid_finish
  have hABFA : AB ≠ FA := by euclid_finish
  have hFABC : FA ≠ BC := by euclid_finish
  have hangle : ∠ b:a:f > ∠ a:f:b := by euclid_finish
  euclid_apply (proposition_19 b a f AB FA BC)
  euclid_finish

end Elements.Book1
