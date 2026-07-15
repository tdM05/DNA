import SystemE

namespace Elements.Book3

-- Mixed corner: b opposite side of AD from e0 but d same side of AB as e0.  As with hFG_int_AE_hos_tf this
-- side-combination is inconsistent with b,d opposite across AE and both ⊥ ae0 (AB = AD).
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hos_ft
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : ¬ b.sameSide d AE)
    (h4 : ¬ b.sameSide e0 AD) (h5 : d.sameSide e0 AB) :
    False := by
  have hFG_int_AE_he0_offAB : ¬ e0.onLine AB := by sorry
  euclid_apply (extend_point AB b a) as b1
  euclid_apply (perpendicular_onlyif b b1 a e0 AB)
  euclid_finish

end Elements.Book3
