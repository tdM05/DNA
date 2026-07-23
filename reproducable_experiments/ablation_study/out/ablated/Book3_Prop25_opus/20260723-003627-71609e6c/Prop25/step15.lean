import SystemE

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step15 (a b c e : Point)
    (h1 : |(a─e)| = |(b─e)|) (h2 : |(b─e)| = |(c─e)|) :
    |(a─e)| = |(e─b)| ∧ |(e─b)| = |(e─c)| := by
  euclid_finish

end Elements.Book3
