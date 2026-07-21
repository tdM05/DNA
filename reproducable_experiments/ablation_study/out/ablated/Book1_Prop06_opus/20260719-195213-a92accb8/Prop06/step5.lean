import SystemE

namespace Elements.Book1

theorem helper_1_6_step5 (a b c d : Point)
    (h1 : |(b─d)| = |(a─c)|) :
    |(d─b)| = |(a─c)| ∧ |(b─c)| = |(c─b)| := by
  euclid_finish

end Elements.Book1
