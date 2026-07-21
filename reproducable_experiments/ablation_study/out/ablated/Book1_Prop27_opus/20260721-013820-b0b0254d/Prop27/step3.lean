import SystemE

namespace Elements.Book1

theorem helper_1_27_step3 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : ∠ a:e:f = ∠ e:f:d)
    (h2 : g.onLine FD) (h3 : d.onLine FD) (h4 : f.onLine FD)
    (h5 : f.onLine EF) (h6 : e.onLine EF)
    (h7 : e.onLine AE) (h8 : a.onLine AE) (h9 : b.onLine AE)
    (h10 : between a e b) (h11 : a.opposingSides d EF)
    (h12 : g.sameSide b EF) (h13 : f ≠ d) :
    ∠ a:e:f = ∠ e:f:g := by
  euclid_finish

end Elements.Book1
