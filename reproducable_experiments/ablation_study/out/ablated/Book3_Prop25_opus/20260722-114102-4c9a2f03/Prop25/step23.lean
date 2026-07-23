import SystemE

namespace Elements.Book3

theorem helper_3_25_step23 (b e : Point) (DB AC : Line)
    (h1 : e.onLine DB ∧ e.sameSide b AC) :
    b.sameSide e AC := by
  euclid_finish

end Elements.Book3
