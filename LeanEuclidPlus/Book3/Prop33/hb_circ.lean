import SystemE

namespace Elements.Book3

-- b is on the circle (centre g, radius ga): ga = gb (SAS, hb_circ_gab), and a is on the circle.
-- (g is off AB — else g ∈ AE ∩ AB = {a}, contradicting g ≠ a; uses e0 ∉ AB so AE ≠ AB.)
set_option systemE.solverTime 30 in
theorem helper_3_33_hb_circ
    (a b c₁ c c₂ d e0 f g g0 : Point) (AB AD AE FG GB : Line) (α : Circle)
    (hne : a ≠ b) (hc1c : c₁ ≠ c) (hcc2 : c ≠ c₂)
    (hpos : 0 < ∠ c₁:c:c₂)
    (hlt2 : ∠ c₁:c:c₂ < ∟ + ∟) (hnrt : ∠ c₁:c:c₂ ≠ ∟)
    (haab : a.onLine AB) (hbab : b.onLine AB)
    (haad : a.onLine AD) (hdad : d.onLine AD) (he0offAD : ¬ e0.onLine AD)
    (hperp_e : ∠ d:a:e0 = ∟) (hdab : ∠ d:a:b = ∠ c₁:c:c₂) (hadd : d ≠ a)
    (haAE : a.onLine AE) (he0AE : e0.onLine AE) (hgAE : g.onLine AE)
    (hafb : between a f b) (haffb : |(a─f)| = |(f─b)|)
    (hg0off : ¬ g0.onLine AB) (hperp_g : ∠ a:f:g0 = ∟)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hgFG : g.onLine FG)
    (hgcen : g.isCentre α) (hacirc : a.onCircle α) (hga : g ≠ a) (hgb : g ≠ b)
    (hgGB : g.onLine GB) (hbGB : b.onLine GB) :
    b.onCircle α := by
  have hFG_int_AE_he0off : ¬ e0.onLine AB := by sorry
  have hgoffAB : ¬ g.onLine AB := by euclid_finish
  have hb_circ_gab : |(g─a)| = |(g─b)| := by sorry
  euclid_finish

end Elements.Book3
