import SystemE
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step2 (a b e f g h k : Point) (AB EF GK : Line)
    (h1 : g.onLine AB) (h2 : a.onLine AB) (h3 : b.onLine AB) (h4 : between a g b)
    (h5 : h.onLine EF) (h6 : e.onLine EF) (h7 : f.onLine EF) (h8 : between e h f)
    (h9 : g.onLine GK) (h10 : h.onLine GK) (h11 : k.onLine GK) (h12 : between g h k)
    (h13 : e.sameSide a GK) (h14 : EF ≠ AB)
    (h15 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF)) :
    ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (extend_point GK h g) as p
  euclid_apply (proposition_29 a b e f p k g h AB EF GK)
  euclid_finish

end Elements.Book1
