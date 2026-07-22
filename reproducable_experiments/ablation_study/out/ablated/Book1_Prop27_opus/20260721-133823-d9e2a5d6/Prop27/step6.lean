import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem helper_1_27_step6 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : ∠ a:e:f = ∠ e:f:d)
    (h2 : f.onLine FD) (h3 : g.onLine FD) (h4 : d.onLine FD)
    (h5 : f.onLine EF) (h6 : e.onLine EF) (h7 : e ≠ f) (h8 : f ≠ d)
    (h9 : a.onLine AE) (h10 : e.onLine AE) (h11 : g.onLine AE) (h12 : b.onLine AE)
    (h13 : between a e b)
    (h14 : ¬(a.onLine EF)) (h15 : ¬(d.onLine EF)) (h16 : ¬(a.sameSide d EF)) :
    ¬(g.opposingSides b EF) := by
  intro hopp
  euclid_apply (proposition_16 f g e b FD AE EF)
  euclid_finish

end Elements.Book1
