import SystemE
import Book1.Prop27.Main
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step2 (a b e f g h k : Point) (AB EF GK : Line)
  (hasm : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))
  (f4 : g.onLine GK) (f7 : h.onLine GK) (f9 : a.onLine AB) (f10 : b.onLine AB)
  (f11 : between a g b) (f12 : e.onLine EF) (f13 : e.sameSide a GK) (f14 : f.onLine EF)
  (f15 : between e h f) (f22 : EF ≠ AB) (f23 : ¬(AB.intersectsLine EF))
  (fhc : between g h k)
  : ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (extend_point GK h g) as p
  euclid_apply (extend_point GK g h) as q
  euclid_apply (proposition_29 a b e f p q g h AB EF GK)
  euclid_finish

end Elements.Book1
