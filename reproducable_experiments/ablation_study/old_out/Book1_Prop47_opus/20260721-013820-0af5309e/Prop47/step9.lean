import SystemE

namespace Elements.Book1

theorem helper_1_47_step9 (a b c d f : Point)
    (h1 : |(d─b)| = |(b─c)|) (h2 : |(f─b)| = |(b─a)|) :
    |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)| := by
  euclid_finish

end Elements.Book1
