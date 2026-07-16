import SystemE

namespace Elements.Book3

-- b and d on OPPOSITE sides of AE, both ⊥ ray ae0 at a: rays ab, ad are opposite, ∠b:a:d = 2∟.
-- Pin e0's sides of AD and AB (4 corners) so the interior-ray (e0 or its reflection e1) has
-- both sum_angles_onlyif conditions available.
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hcon_os
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : ¬ b.sameSide d AE) :
    False := by
  by_cases h4 : b.sameSide e0 AD
  · by_cases h5 : d.sameSide e0 AB
    · have hFG_int_AE_hos_tt : False := by sorry
      exact hFG_int_AE_hos_tt
    · have hFG_int_AE_hos_tf : False := by sorry
      exact hFG_int_AE_hos_tf
  · by_cases h5 : d.sameSide e0 AB
    · have hFG_int_AE_hos_ft : False := by sorry
      exact hFG_int_AE_hos_ft
    · have hFG_int_AE_hos_ff : False := by sorry
      exact hFG_int_AE_hos_ff

end Elements.Book3
