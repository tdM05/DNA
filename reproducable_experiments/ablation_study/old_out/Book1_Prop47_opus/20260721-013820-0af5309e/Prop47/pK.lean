import SystemE

namespace Elements.Book1

-- foot perpendicular angle: ∠ a:m:c = ∟ from AL ∥ BD, BD ⊥ BC
theorem probe_K (a b c d m : Point) (BC BD AL : Line)
    (h1 : b.onLine BC) (h2 : c.onLine BC) (h3 : b ≠ c)
    (h4 : b.onLine BD) (h5 : d.onLine BD)
    (h6 : ∠ c:b:d = ∟)
    (h7 : a.onLine AL) (h8 : m.onLine AL) (h9 : m.onLine BC)
    (h10 : ¬(AL.intersectsLine BD)) (h11 : ¬(a.onLine BC))
    (h12 : a ≠ m) (h13 : m ≠ c) (h14 : m ≠ b) :
    ∠ a:m:c = ∟ := by
  euclid_finish

end Elements.Book1
