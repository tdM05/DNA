import SystemE

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step14 (a b c e : Point)
    (h1 : |(a─e)| = |(b─e)|) (h2 : |(a─e)| = |(c─e)|) :
    |(b─e)| = |(c─e)| := by
  euclid_finish

end Elements.Book3
