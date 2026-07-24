import SystemE

namespace Elements.Book3

theorem helper_3_25_step1 (a c d : Point)
    (h1 : between a d c) (h2 : |(a─d)| = |(d─c)|) :
    between a d c ∧ |(a─d)| = |(d─c)| := by
  euclid_finish

end Elements.Book3
