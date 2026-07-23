import SystemE

namespace Elements.Book1

-- between b m c from the triangle angle-sum and foot-perpendicular angles
theorem probe_I2 (a b c m : Point) (BC AL : Line)
    (h1 : b.onLine BC) (h2 : c.onLine BC) (h3 : b ≠ c)
    (h4 : a.onLine AL) (h5 : m.onLine AL) (h6 : m.onLine BC) (h7 : ¬(a.onLine BC))
    (h8 : b ≠ m) (h9 : c ≠ m) (h10 : a ≠ m)
    (h11 : ∠ a:m:b = ∟) (h12 : ∠ a:m:c = ∟)
    (h13 : ∠ b:a:c = ∟)
    (h14 : ∠ a:b:c + ∠ b:c:a + ∠ c:a:b = ∟ + ∟) :
    between b m c := by
  euclid_finish

end Elements.Book1
