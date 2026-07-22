import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem helper_1_27_step4 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : f.onLine FD) (h2 : g.onLine FD) (h3 : g.onLine AE) (h4 : e.onLine AE)
    (h5 : e.onLine EF) (h6 : f.onLine EF) (h7 : e ≠ f)
    (h8 : a.onLine AE) (h9 : d.onLine FD)
    (h10 : ¬(a.onLine EF)) (h11 : ¬(d.onLine EF))
    (h12 : g.sameSide b EF) (h13 : between a e b) (h14 : b.onLine AE)
    (h15 : ∠ a:e:f = ∠ e:f:g) :
    False := by
  euclid_apply (proposition_16 f g e a FD AE EF)
  euclid_finish

end Elements.Book1
