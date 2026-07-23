import SystemE

namespace Elements.Book3

theorem helper_3_25_step12 (a c d e : Point) (AC : Line)
    (h1 : |(a─d)| = |(c─d)|) (h2 : ∠ a:d:e = ∠ c:d:e)
    (h3 : ∠ a:d:e = ∟) (h4 : ∠ c:d:e = ∟)
    (h5 : between a d c) (h6 : a.onLine AC) (h7 : c.onLine AC)
    (h8 : ¬e.onLine AC) (hde : d ≠ e) :
    |(a─e)| = |(c─e)| := by
  euclid_finish

end Elements.Book3
