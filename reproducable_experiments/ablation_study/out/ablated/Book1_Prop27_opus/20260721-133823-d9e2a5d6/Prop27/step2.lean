import SystemE

namespace Elements.Book1

theorem helper_1_27_step2 (b g : Point) (AE FD EF : Line)
    (h1 : g.onLine AE) (h2 : g.onLine FD) (h3 : g.sameSide b EF) :
    g.onLine AE ∧ g.onLine FD ∧ g.sameSide b EF := by
  euclid_finish

end Elements.Book1
