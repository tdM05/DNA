import SystemE
import Book1.Prop29.Main

namespace Elements.Book1

theorem helper_1_30_step3 (a c d e f g h k : Point) (CD EF GK : Line)
    (h1 : e.onLine EF) (h2 : f.onLine EF) (h3 : between e h f)
    (h4 : c.onLine CD) (h5 : d.onLine CD) (h6 : between c k d)
    (h7 : g.onLine GK) (h8 : h.onLine GK) (h9 : k.onLine GK)
    (h10 : between g h k) (h11 : e.sameSide a GK) (h12 : c.sameSide a GK)
    (h13 : h.onLine EF) (h14 : CD ≠ EF)
    (h15 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF)) :
    ∠ g:h:f = ∠ g:k:d := by
  euclid_apply (extend_point GK h k) as p
  euclid_apply (proposition_29 e f c d g p h k EF CD GK)
  euclid_finish

end Elements.Book1
