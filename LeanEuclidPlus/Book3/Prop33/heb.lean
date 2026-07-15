import SystemE

namespace Elements.Book3

-- e ≠ b: e ∈ AE and b ∈ AB; if e = b then b ∈ AE ∩ AB = {a} (AE ≠ AB since e0 ∉ AB), so b = a,
-- contradicting a ≠ b.
set_option systemE.solverTime 30 in
theorem helper_3_33_heb
    (a b c₁ c c₂ d e0 e : Point) (AB AD AE : Line)
    (hne : a ≠ b) (hc1c : c₁ ≠ c) (hcc2 : c ≠ c₂) (hpos : 0 < ∠ c₁:c:c₂) (hacute : ∠ c₁:c:c₂ < ∟)
    (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (haab : a.onLine AB) (hbab : b.onLine AB)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hperp_e : ∠ d:a:e0 = ∟) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hadd : d ≠ a)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (heAE : e.onLine AE) :
    e ≠ b := by
  have hFG_int_AE_he0off : ¬ e0.onLine AB := by sorry
  euclid_finish

end Elements.Book3
