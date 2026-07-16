import SystemE

namespace Elements.Book3

-- b,d opposite sides of AE; b opposite e0 across AD and d opposite e0 across AB.  The reflection
-- e1 (between e0 a e1) is the interior ray: b.sameSide e1 AD, d.sameSide e1 AB, and
-- ∠b:a:e1 = ∠d:a:e1 = ∟, so ∠b:a:d = ∠b:a:e1 + ∠e1:a:d = 2∟, contradicting ∠d:a:b < ∟.
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hos_ff
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (heq : ∠ e0:a:b = ∟) (hbd : ¬ b.sameSide d AE)
    (h4 : ¬ b.sameSide e0 AD) (h5 : ¬ d.sameSide e0 AB) :
    False := by
  euclid_apply (extend_point AE e0 a) as e1
  have hFG_int_AE_hb_ff : b.sameSide e1 AD := by sorry
  have hFG_int_AE_hd_ff : d.sameSide e1 AB := by sorry
  euclid_apply (perpendicular_onlyif e0 e1 a b AE)
  euclid_apply (perpendicular_onlyif e0 e1 a d AE)
  euclid_apply (sum_angles_onlyif a b d e1 AB AD)
  euclid_finish

end Elements.Book3
