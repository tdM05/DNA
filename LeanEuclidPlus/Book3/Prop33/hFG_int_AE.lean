import SystemE

namespace Elements.Book3

-- FG (⊥ AB at midpoint f) meets AE (through a, with AE not ⊥ AB since ∠d:a:b ∈ (0,∟)).
-- Euclid's Postulate 5 (`lines_intersect`): the lines converge on the side of the transversal
-- AB where the co-interior angles sum to < 2∟.  The perpendicular reps e0, g0 land on arbitrary
-- sides, so we case-split to the acute-direction rep of AE and the matching-side rep of FG,
-- each branch discharged in its own leaf (one `lines_intersect` apiece).
set_option systemE.solverTime 30 in
theorem helper_3_33_hFG_int_AE
    (a b c₁ c c₂ d e0 f g0 : Point) (AB AD AE FG : Line)
    (hab : a.onLine AB) (hbb : b.onLine AB) (hne : a ≠ b) (hadd : d ≠ a)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hperp_e : ∠ d:a:e0 = ∟)
    (haae : a.onLine AE) (heae : e0.onLine AE)
    (hafb : between a f b)
    (hg0off : ¬g0.onLine AB) (hperp_g : ∠ a:f:g0 = ∟)
    (hffg : f.onLine FG) (hg0fg : g0.onLine FG)
    (hdab : ∠ d:a:b = ∠ c₁:c:c₂)
    (hpos : 0 < ∠ c₁:c:c₂) (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟) :
    FG.intersectsLine AE := by
  have hfb : f.onLine AB := by euclid_finish
  have hafne : a ≠ f := by euclid_finish
  have hFG_int_AE_he0off : ¬ e0.onLine AB := by sorry
  by_cases hpe : ∠ e0:a:b < ∟
  · by_cases hqs : e0.sameSide g0 AB
    · have hFG_int_AE_hbr1 : FG.intersectsLine AE := by sorry
      exact hFG_int_AE_hbr1
    · have hFG_int_AE_hbr2 : FG.intersectsLine AE := by sorry
      exact hFG_int_AE_hbr2
  · euclid_apply (extend_point AE e0 a) as e1
    have hFG_int_AE_he1off : ¬ e1.onLine AB := by sorry
    by_cases hqs : e1.sameSide g0 AB
    · have hFG_int_AE_hbr3 : FG.intersectsLine AE := by sorry
      exact hFG_int_AE_hbr3
    · have hFG_int_AE_hbr4 : FG.intersectsLine AE := by sorry
      exact hFG_int_AE_hbr4

end Elements.Book3
