import SystemE

namespace Elements.Book1

theorem alceA (a p m c : Point) (BC AL : Line)
    (h1 : a.onLine AL) (h2 : m.onLine AL) (h3 : p.onLine AL)
    (h4 : m.onLine BC) (h5 : c.onLine BC)
    (h6 : ∠ a:m:c = ∟) (h7 : p ≠ m) (h8 : a ≠ m) (h9 : m ≠ c)
    (h10 : ¬(a.onLine BC)) :
    ∠ p:m:c = ∟ := by
  euclid_finish

theorem alceApc (b e p m c : Point) (BC CE : Line)
    (h4 : m.onLine BC) (h5 : c.onLine BC) (hb : b.onLine BC)
    (h1 : c.onLine CE) (h2 : e.onLine CE) (h3 : p.onLine CE)
    (h6 : ∠ b:c:e = ∟) (h7 : p ≠ c) (h8 : m ≠ c) (h9 : b ≠ c)
    (h10 : ¬(b.onLine CE)) :
    ∠ p:c:m = ∟ := by
  euclid_finish

end Elements.Book1
