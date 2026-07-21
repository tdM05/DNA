import SystemE

namespace Elements.Book1

theorem helper_1_20_step8 (a b c d : Point)
    (h1 : between b a d) (h2 : |(d─b)| > |(b─c)|) (h3 : |(a─d)| = |(a─c)|) :
    |(b─a)| + |(a─c)| > |(b─c)| := by
  euclid_finish

end Elements.Book1
