import SystemE

namespace Elements.Book3

theorem helper_3_25_step19 (a b c d : Point)
    (h1 : ∠ a:b:d = ∠ b:a:d)
    (h2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|) :
    |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  euclid_finish

end Elements.Book3
