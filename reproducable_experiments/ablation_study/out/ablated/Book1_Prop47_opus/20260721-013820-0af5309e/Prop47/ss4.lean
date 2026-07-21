import SystemE

namespace Elements.Book1

-- c.sameSide a BF, since AC ∥ BF and a,c both on AC
theorem helper_1_47_ss4 (a b c f : Point) (AB BC AC BF : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h10 : b.onLine BF) (h11 : f.onLine BF)
    (h16 : ∠ a:b:f = ∟) (h18 : ∠ b:a:c = ∟)
    (h21 : ¬(BF.intersectsLine AC))
    (h26 : ¬(a.onLine BF)) (h27 : ¬(c.onLine BF)) :
    c.sameSide a BF := by
  euclid_finish

end Elements.Book1
