import SystemE
import Book1.Prop27.Main
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_othercases (a b c d e f g h k : Point) (AB CD EF GK : Line)
  (f1 : g.onLine AB) (f2 : k.onLine CD) (f3 : g ≠ k) (f4 : g.onLine GK) (f5 : k.onLine GK)
  (f6 : h.onLine EF) (f7 : h.onLine GK) (f8 : g ≠ a) (f9 : a.onLine AB) (f10 : b.onLine AB)
  (f11 : between a g b) (f12 : e.onLine EF) (f13 : e.sameSide a GK) (f14 : f.onLine EF)
  (f15 : between e h f) (f16 : c.onLine CD) (f17 : c.sameSide a GK) (f18 : d.onLine CD)
  (f19 : between c k d) (f21 : CD ≠ EF) (f22 : EF ≠ AB) (f23 : ¬(AB.intersectsLine EF))
  (f24 : ¬(CD.intersectsLine EF))
  (hnhc : ¬(between g h k))
  : ¬(AB.intersectsLine CD) := by
  have hopp : a.opposingSides d GK := by euclid_finish
  have hang : ∠ a:g:k = ∠ g:k:d := by
    euclid_apply (extend_point GK h g) as p1
    euclid_apply (extend_point GK g h) as q1
    euclid_apply (proposition_29 a b e f p1 q1 g h AB EF GK)
    euclid_apply (extend_point GK k h) as p2
    euclid_apply (extend_point GK h k) as q2
    euclid_apply (proposition_29 e f c d p2 q2 h k EF CD GK)
    by_cases hA : between h g k
    · euclid_finish
    · by_cases hB : between g k h
      · euclid_finish
      · euclid_finish
  euclid_apply (proposition_27 a d g k AB CD GK)

end Elements.Book1
