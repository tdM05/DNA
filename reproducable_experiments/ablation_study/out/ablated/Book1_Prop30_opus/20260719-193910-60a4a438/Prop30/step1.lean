import SystemE
import Book1.Prop27.Main
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step1 (a b c d e f g h k : Point) (AB CD EF GK : Line)
  (f11 : between a g b) (f4 : g.onLine GK) (f9 : a.onLine AB) (f10 : b.onLine AB)
  (f15 : between e h f) (f7 : h.onLine GK) (f12 : e.onLine EF) (f14 : f.onLine EF)
  (f19 : between c k d) (f5 : k.onLine GK) (f16 : c.onLine CD) (f18 : d.onLine CD)
  : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by
  euclid_finish

end Elements.Book1
