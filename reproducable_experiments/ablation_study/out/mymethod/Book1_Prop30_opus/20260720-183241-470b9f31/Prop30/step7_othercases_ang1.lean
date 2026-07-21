import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_ang1 (AB EF GK : Line) (a b e f g h : Point)
  (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hagb : between a g b)
  (he_ef : e.onLine EF) (hf_ef : f.onLine EF) (hehf : between e h f)
  (hea_ss : e.sameSide a GK)
  (hab_ef : ¬AB.intersectsLine EF) (hne_ef_ab : EF ≠ AB) :
  ∠ a:g:h = ∠ g:h:f := by
  have hgh_ne : g ≠ h := by
    intro heq
    euclid_apply (intersection_lines_common_point g AB EF)
    euclid_finish
  -- extension points on GK: p1 before g (between p1 g h), q1 beyond h (between g h q1)
  euclid_apply (extend_point GK h g) as p1
  euclid_apply (extend_point GK g h) as q1
  -- b and f on the same side of GK
  have hbf : b.sameSide f GK := by euclid_finish
  -- proposition 1.29 on parallels AB, EF with transversal GK (crossings g, h)
  euclid_apply (proposition_29 a b e f p1 q1 g h AB EF GK)
  euclid_finish

end Elements.Book1
