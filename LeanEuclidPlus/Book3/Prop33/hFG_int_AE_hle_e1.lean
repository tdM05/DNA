import SystemE
import Mathlib.Tactic.Linarith

namespace Elements.Book3

-- In the branch ∠e0:a:b ≥ ∟, the AE-extension e1 (a between e0, e1) is the acute rep.
-- ∠e0:a:b + ∠e1:a:b = 2∟ (straight line e0-a-e1, b off it), and ∠e0:a:b ≠ ∟ (else AE ⊥ AB,
-- which with AD ⊥ AE forces ∠d:a:b ∈ {0,2∟}), so ∠e0:a:b > ∟ and ∠e1:a:b < ∟.
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hle_e1
    (a b c₁ c c₂ d e0 e1 : Point) (AD AE AB : Line)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a) (he0off : ¬ e0.onLine AD)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (he0offAB : ¬ e0.onLine AB)
    (he1 : between e0 a e1) (hperp_e : ∠ d:a:e0 = ∟)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (hpe2 : ¬ ∠ e0:a:b < ∟) :
    ∠ e1:a:b < ∟ := by
  have hFG_int_AE_hsup_e1 : ∠ e0:a:b + ∠ e1:a:b = ∟ + ∟ := by sorry
  have hFG_int_AE_hne_e0 : ∠ e0:a:b ≠ ∟ := by sorry
  have hge : ∟ ≤ ∠ e0:a:b := not_lt.mp hpe2
  rcases lt_or_gt_of_ne hFG_int_AE_hne_e0 with h | h
  · linarith
  · linarith

end Elements.Book3
