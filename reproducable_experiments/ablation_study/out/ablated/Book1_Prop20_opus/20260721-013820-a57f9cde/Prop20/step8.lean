import SystemE

namespace Elements.Book1

theorem helper_1_20_step8 (a b c d : Point)
    (h1 : |(d─b)| > |(b─c)|) (h2 : between b a d) (h3 : |(d─a)| = |(a─c)|) :
    |(b─a)| + |(a─c)| > |(b─c)| := by
  euclid_finish

end Elements.Book1
