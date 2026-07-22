import SystemE

namespace Elements.Book1

theorem helper_1_27_step3 (a b d e f g : Point) (AE FD EF : Line)
    (h1 : ∠ a:e:f = ∠ e:f:d)
    (h2 : f.onLine FD) (h3 : d.onLine FD) (h4 : g.onLine FD) (h5 : f ≠ d)
    (h6 : g.sameSide b EF)
    (h7 : between a e b)
    (h8 : e.onLine EF) (h9 : f.onLine EF) (h10 : e ≠ f)
    (h11 : ¬(a.onLine EF)) (h12 : ¬(d.onLine EF)) (h13 : ¬(a.sameSide d EF))
    (h14 : a.onLine AE) (h15 : e.onLine AE) (h16 : g.onLine AE) (h17 : b.onLine AE) :
    ∠ a:e:f = ∠ e:f:g := by
  euclid_finish

end Elements.Book1
