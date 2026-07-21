import SystemE

namespace Elements.Book1

theorem helper_1_27_step1 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : AE.intersectsLine FD)
    (h2 : g.onLine AE) (h3 : g.onLine FD)
    (h4 : e.onLine AE) (h5 : e.onLine EF)
    (h6 : f.onLine FD) (h7 : f.onLine EF)
    (h8 : e ≠ f) (h9 : a.onLine AE) (h10 : a.opposingSides d EF)
    (h11 : d.onLine FD) (h12 : between a e b) (h13 : b.onLine AE) :
    g.sameSide b EF ∨ g.opposingSides b EF := by
  euclid_finish

end Elements.Book1
