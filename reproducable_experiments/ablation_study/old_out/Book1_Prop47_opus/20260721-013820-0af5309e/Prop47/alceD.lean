import SystemE

namespace Elements.Book1

theorem alceD (a b c e m : Point) (BC CE AL : Line)
    (h1 : a.onLine AL) (h2 : m.onLine AL)
    (h3 : m.onLine BC) (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c) (h7 : m ≠ c)
    (h8 : c.onLine CE) (h9 : e.onLine CE)
    (h10 : ∠ a:m:c = ∟) (h11 : ∠ b:c:e = ∟)
    (h12 : ¬(a.onLine BC)) (h13 : ¬(a.onLine CE)) (h14 : ¬(c.onLine AL)) (h15 : a ≠ m) :
    ¬(AL.intersectsLine CE) := by
  euclid_finish

end Elements.Book1
