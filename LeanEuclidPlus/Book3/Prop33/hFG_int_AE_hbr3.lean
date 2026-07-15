import SystemE

namespace Elements.Book3

-- Post-5 branch: ∠e0:a:b ≥ ∟, so e1 (AE extended past a) is the acute rep (hFG_int_AE_hle_e1).
-- g0 is already on e1's side of AB.
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE_hbr3
    (a b c₁ c c₂ d e0 e1 f g0 : Point) (AB AD AE FG : Line)
    (haae : a.onLine AE) (he0ae : e0.onLine AE) (he1ae : e1.onLine AE)
    (he1 : between e0 a e1)
    (haad : a.onLine AD) (hdad : d.onLine AD) (hadd : d ≠ a) (he0off : ¬ e0.onLine AD) (hperp_e : ∠ d:a:e0 = ∟)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (he0offAB : ¬ e0.onLine AB)
    (hfb : f.onLine AB) (hafb : between a f b)
    (hperp_g : ∠ a:f:g0 = ∟)
    (hffg : f.onLine FG) (hg0fg : g0.onLine FG) (hg0off : ¬ g0.onLine AB)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (hpe2 : ¬ ∠ e0:a:b < ∟) (hqs : e1.sameSide g0 AB) (hafne : a ≠ f) :
    FG.intersectsLine AE := by
  have hFG_int_AE_hle_e1 : ∠ e1:a:b < ∟ := by sorry
  have hsum : ∠ e1:a:f + ∠ a:f:g0 < ∟ + ∟ := by euclid_finish
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  euclid_apply (lines_intersect e1 a f g0 AE AB FG) as gg
  have hfgne : FG ≠ AE := fun h => haoffFG (h ▸ haae)
  euclid_apply (intersection_lines_common_point gg FG AE)
  assumption

end Elements.Book3
