import SystemE
import Book1.Prop19.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_big (a b c e e' : Point) (AB BC AC EC : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hc_AC : c.onLine AC) (ha_AC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (he'_AB : e'.onLine AB) (h_abe' : between a b e') (h_bee' : between b e e')
    (he_EC : e.onLine EC) (hc_EC : c.onLine EC)
    (hstep9_gt : ∠ a:c:e > ∠ b:e:c) :
    |(e─a)| > |(a─c)| := by
  have he_AB : e.onLine AB := by euclid_finish
  have hcAB : ¬ c.onLine AB := by euclid_finish
  have hae : a ≠ e := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hACEC : AC ≠ EC := by euclid_finish
  have hECAB : EC ≠ AB := by euclid_finish
  have hangle : ∠ a:c:e > ∠ c:e:a := by euclid_finish
  euclid_apply (proposition_19 a c e AC EC AB)
  euclid_finish

end Elements.Book1
