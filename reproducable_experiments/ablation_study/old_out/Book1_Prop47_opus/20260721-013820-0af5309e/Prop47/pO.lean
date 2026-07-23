import SystemE

namespace Elements.Book1

-- between b m c from the straightness facts between c a g / between b a h
theorem probe_O (a b c g h m : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC)
    (h9 : ∠ b:a:c = ∟)
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h18 : m.onLine BC)
    (h19 : between c a g) (h20 : between b a h)
    (h21 : ¬(a.onLine BC)) (h22 : b ≠ m) (h23 : c ≠ m) :
    between b m c := by
  euclid_finish

end Elements.Book1
