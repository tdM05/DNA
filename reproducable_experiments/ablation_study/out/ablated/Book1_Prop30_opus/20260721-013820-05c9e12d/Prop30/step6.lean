import SystemE

namespace Elements.Book1

theorem helper_1_30_step6 (a c d k : Point) (CD GK : Line)
    (h1 : c.sameSide a GK) (h2 : between c k d) (h3 : k.onLine GK)
    (h4 : c.onLine CD) (h5 : d.onLine CD) :
    a.opposingSides d GK := by
  euclid_finish

end Elements.Book1
