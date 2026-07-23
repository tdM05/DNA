import SystemE

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step13 (a b e : Point)
    (h1 : |(e─b)| = |(e─a)|) :
    |(a─e)| = |(b─e)| := by
  euclid_finish

end Elements.Book3
