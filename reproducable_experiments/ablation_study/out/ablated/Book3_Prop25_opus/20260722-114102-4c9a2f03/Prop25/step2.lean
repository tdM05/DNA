import SystemE

namespace Elements.Book3

theorem helper_3_25_step2 (a b c d : Point) (AC : Line)
    (h1 : a.onLine AC) (h2 : c.onLine AC) (h3 : ¬b.onLine AC)
    (h4 : |(a─b)| = |(c─b)|) (h5 : between a d c) (h6 : |(a─d)| = |(d─c)|)
    (h7 : a ≠ c) :
    ∠ a:d:b = ∟ := by
  euclid_finish

end Elements.Book3
