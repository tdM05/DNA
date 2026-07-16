import SystemE

namespace Elements.Book3

-- e1 is the reflection of e0 across a on AE (between e0 a e1); a is on AD so e0, e1 are on
-- opposite sides of AD.  b is opposite e0 across AD (¬h4), hence on the same side as e1.
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hb_ff
    (a b c₁ c c₂ d e0 e1 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (he1 : between e0 a e1) (h4 : ¬ b.sameSide e0 AD) :
    b.sameSide e1 AD := by
  have hFG_int_AE_hb_offAD : ¬ b.onLine AD := by sorry
  euclid_finish

end Elements.Book3
