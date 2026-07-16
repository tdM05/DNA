import SystemE

namespace Elements.Book3

-- ∠e0:a:b ≠ ∟: if ∠e0:a:b = ∟ then ray ab ⊥ AE at a; with ray ad ⊥ AE at a (∠d:a:e0 = ∟),
-- rays ab, ad coincide (∠d:a:b = 0) or are opposite (∠d:a:b = 2∟) — both contradict 0<∠d:a:b<∟.
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hne_e0
    (a b c₁ c c₂ d e0 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟) :
    ∠ e0:a:b ≠ ∟ := by
  intro heq
  by_cases hbd : b.sameSide d AE
  · have hFG_int_AE_hcon_ss : False := by sorry
    exact hFG_int_AE_hcon_ss
  · have hFG_int_AE_hcon_os : False := by sorry
    exact hFG_int_AE_hcon_os

end Elements.Book3
