import SystemE

namespace Elements.Book3

theorem helper_3_25_step10 (a c d e : Point)
    (h1 : |(a─d)| = |(d─c)|) (h2 : |(d─e)| = |(d─e)|) :
    |(a─d)| = |(c─d)| ∧ |(d─e)| = |(d─e)| := by
  euclid_finish

end Elements.Book3
