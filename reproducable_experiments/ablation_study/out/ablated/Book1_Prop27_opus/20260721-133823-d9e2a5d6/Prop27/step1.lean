import SystemE

namespace Elements.Book1

theorem helper_1_27_step1 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : a.onLine AE) (h2 : e.onLine AE) (h3 : b.onLine AE)
    (h4 : between a e b)
    (h5 : g.onLine AE) (h6 : g.onLine FD)
    (h7 : e.onLine EF) (h8 : f.onLine EF) (h9 : e ≠ f)
    (h10 : f.onLine FD) (h11 : d.onLine FD)
    (h12 : ¬(a.onLine EF)) (h13 : ¬(d.onLine EF))
    (h14 : AE.intersectsLine FD) :
    g.sameSide b EF ∨ g.opposingSides b EF := by
  euclid_finish

end Elements.Book1
