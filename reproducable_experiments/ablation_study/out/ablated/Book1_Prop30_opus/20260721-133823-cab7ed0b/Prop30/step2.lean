import SystemE
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step2 (a b e f g h k : Point) (AB EF GK : Line)
    (hass : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : between a g b)
    (h4 : e.onLine EF) (h5 : f.onLine EF) (h6 : between e h f)
    (h7 : g.onLine GK) (h8 : h.onLine GK) (h9 : k.onLine GK)
    (h10 : e.sameSide a GK) (h11 : between g h k) :
    ∠ a:g:k = ∠ g:h:f := by
  euclid_apply (extend_point GK h g) as m
  euclid_apply (proposition_29 a b e f m k g h AB EF GK)
  euclid_finish

end Elements.Book1
