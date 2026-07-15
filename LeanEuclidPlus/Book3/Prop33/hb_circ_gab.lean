import SystemE
import Book1.Prop04.Main

namespace Elements.Book3

open Elements.Book1

-- SAS: triangles f-a-g and f-b-g are congruent (fa = fb, fg common, ∠afg = ∠bfg = ∟), so ga = gb.
set_option systemE.solverTime 30 in
theorem helper_3_33_hb_circ_gab
    (a b f g g0 : Point) (AB FG GB : Line)
    (haab : a.onLine AB) (hbab : b.onLine AB) (hafb : between a f b) (haffb : |(a─f)| = |(f─b)|)
    (hfFG : f.onLine FG) (hg0FG : g0.onLine FG) (hg0off : ¬ g0.onLine AB) (hperp_g : ∠ a:f:g0 = ∟)
    (hgFG : g.onLine FG) (hgGB : g.onLine GB) (hbGB : b.onLine GB)
    (hga : g ≠ a) (hgb : g ≠ b) (hgoffAB : ¬ g.onLine AB) :
    |(g─a)| = |(g─b)| := by
  euclid_apply (line_from_points a g) as AG
  have hafg : ∠ a:f:g = ∟ := by euclid_finish
  have hbfg : ∠ b:f:g = ∟ := by euclid_finish
  have haoffFG : ¬ a.onLine FG := by euclid_finish
  have hboffFG : ¬ b.onLine FG := by euclid_finish
  have hb_circ_gab_tri1 : formTriangle f a g AB AG FG := by sorry
  have hb_circ_gab_tri2 : formTriangle f b g AB GB FG := by sorry
  euclid_apply (proposition_4 f a g f b g AB AG FG AB GB FG)
  euclid_finish

end Elements.Book3
