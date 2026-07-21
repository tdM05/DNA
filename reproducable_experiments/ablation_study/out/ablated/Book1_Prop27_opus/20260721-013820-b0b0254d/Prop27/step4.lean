import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem helper_1_27_step4 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : f.onLine FD) (h2 : g.onLine FD) (h3 : d.onLine FD)
    (h4 : g.onLine AE) (h5 : e.onLine AE) (h6 : a.onLine AE) (h7 : b.onLine AE)
    (h8 : e.onLine EF) (h9 : f.onLine EF)
    (h10 : between a e b) (h11 : g.sameSide b EF)
    (h12 : a.opposingSides d EF) (h13 : e ≠ f)
    (h14 : ∠ a:e:f = ∠ e:f:g) :
    False := by
  euclid_apply (proposition_16 f g e a FD AE EF)
  euclid_finish

end Elements.Book1
