import SystemE

namespace Elements.Book1

theorem helper_1_18_step5 (a b c d : Point) (BC AC : Line)
    (h1 : ∠ a:d:b = ∠ a:b:d)
    (h2 : ∠ a:d:b > ∠ d:c:b)
    (h3 : between a d c)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC) :
    ∠ a:b:d > ∠ b:c:a := by
  euclid_finish

end Elements.Book1
