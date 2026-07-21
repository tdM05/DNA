import SystemE

namespace Elements.Book1

theorem helper_1_20_step1 (a b d d' : Point) (AB : Line)
    (h1 : between b a d') (h2 : between a d d')
    (h3 : a.onLine AB) (h4 : b.onLine AB) (h5 : d'.onLine AB) :
    between b a d := by
  euclid_finish

end Elements.Book1
