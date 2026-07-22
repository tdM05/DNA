import SystemE
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step3 (a c d e f g h k : Point) (EF CD GK : Line)
    (hass : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))
    (h1 : e.onLine EF) (h2 : f.onLine EF) (h3 : between e h f)
    (h4 : c.onLine CD) (h5 : d.onLine CD) (h6 : between c k d)
    (h7 : g.onLine GK) (h8 : h.onLine GK) (h9 : k.onLine GK)
    (h10 : e.sameSide a GK) (h11 : c.sameSide a GK) (h12 : between g h k) :
    ∠ g:h:f = ∠ g:k:d := by
  euclid_apply (extend_point GK h k) as n
  euclid_apply (proposition_29 e f c d g n h k EF CD GK)
  euclid_finish

end Elements.Book1
