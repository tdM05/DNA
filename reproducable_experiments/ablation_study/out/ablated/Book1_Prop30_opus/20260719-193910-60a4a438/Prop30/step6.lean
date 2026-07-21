import SystemE

namespace Elements.Book1

theorem helper_1_30_step6 (a c d g k : Point) (AB CD GK : Line)
  (f17 : c.sameSide a GK) (f19 : between c k d) (f5 : k.onLine GK)
  (f9 : a.onLine AB) (f18 : d.onLine CD) (f16 : c.onLine CD)
  : a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
