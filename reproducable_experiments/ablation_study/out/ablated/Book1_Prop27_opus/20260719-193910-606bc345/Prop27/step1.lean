import SystemE

namespace Elements.Book1

theorem helper_1_27_step1 (a d e f b g : Point) (AE FD EF : Line)
    (hae1 : a.onLine AE) (hae2 : e.onLine AE) (hae3 : a ≠ e)
    (hfd1 : f.onLine FD) (hfd2 : d.onLine FD) (hfd3 : f ≠ d)
    (hef1 : e.onLine EF) (hef2 : f.onLine EF) (hef3 : e ≠ f)
    (hop1 : ¬a.onLine EF) (hop2 : ¬d.onLine EF) (hop3 : ¬(a.sameSide d EF))
    (hang : ∠ a:e:f = ∠ e:f:d)
    (hint : AE.intersectsLine FD)
    (hb1 : b.onLine AE) (hb2 : between a e b)
    (hg1 : g.onLine AE) (hg2 : g.onLine FD) :
    g.sameSide b EF ∨ g.opposingSides b EF := by
  euclid_finish

end Elements.Book1
