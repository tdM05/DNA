import SystemE

namespace Elements.Book1

theorem helper_1_6_step3 (a b c d : Point)
    (h1 : between b d a) (h2 : |(b─d)| = |(a─c)|) :
    between b d a ∧ |(b─d)| = |(a─c)| := by
  euclid_finish

end Elements.Book1
