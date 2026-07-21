import SystemE
import Book1.Prop27.Main
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step3 (a c d e f g h k : Point) (CD EF GK : Line)
  (hasm : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))
  (f5 : k.onLine GK) (f6 : h.onLine EF) (f7 : h.onLine GK) (f12 : e.onLine EF)
  (f13 : e.sameSide a GK) (f14 : f.onLine EF) (f15 : between e h f) (f16 : c.onLine CD)
  (f17 : c.sameSide a GK) (f18 : d.onLine CD) (f19 : between c k d) (f21 : CD ≠ EF)
  (f24 : ¬(CD.intersectsLine EF))
  (fhc : between g h k)
  : ∠ g:h:f = ∠ g:k:d := by
  euclid_apply (extend_point GK k h) as p
  euclid_apply (extend_point GK h k) as q
  euclid_apply (proposition_29 e f c d p q h k EF CD GK)
  euclid_finish

end Elements.Book1
