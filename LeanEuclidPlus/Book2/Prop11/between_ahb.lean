import SystemE

namespace Elements.Book2

set_option systemE.solverTime 30 in
theorem helper_2_11_between_ahb
    (a b c e f f0 h g x : Point) (AB AC AH GH CD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hfAC : f.onLine AC)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hang_bac : ∠ b:a:c = ∟) (hang_fah : ∠ f:a:h = ∟)
    (hbet_aec : between a e c) (hae_ec : |(a─e)| = |(e─c)|)
    (hac_ab : |(a─c)| = |(a─b)|)
    (hbet_caf0 : between c a f0) (hbet_eff0 : between e f f0) (hef_be : |(e─f)| = |(b─e)|)
    (hah_af : |(a─h)| = |(a─f)|)
    (hxoff : ¬ x.onLine AC) (hboff : ¬ b.onLine AC) (hhoff : ¬ h.onLine AC)
    (hxnsb : ¬ x.sameSide b AC) (hhnsx : ¬ h.sameSide x AC) :
    between a h b := by
  -- magnitude tower: |a-f| < |a-b| (Pythagoras on a-e-b + bisection), then the figure forces a-h-b.
  have step8_pyth : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by sorry
  have step8_bisect : |(a─b)| = |(a─e)| + |(a─e)| := by sorry
  have step8_eb : |(e─b)| = |(a─e)| + |(a─f)| := by sorry
  have step8_ahb_mag : |(a─f)| < |(a─b)| := by sorry
  euclid_finish

end Elements.Book2
