import SystemE

namespace Elements.Book1

theorem helper_1_6_step1 (a b c : Point)
    (h1 : |(a─b)| ≠ |(a─c)|) :
    |(a─b)| > |(a─c)| ∨ |(a─c)| > |(a─b)| := by
  euclid_finish

end Elements.Book1
