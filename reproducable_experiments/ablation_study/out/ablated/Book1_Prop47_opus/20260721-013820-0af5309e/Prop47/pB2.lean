import SystemE

namespace Elements.Book1

-- and: is between b m c itself derivable from b.opposingSides c AL ?
theorem probe_B2 (a b c m : Point) (BC AL : Line)
    (h1 : m.onLine AL) (h2 : m.onLine BC)
    (h3 : b.onLine BC) (h4 : c.onLine BC) (h5 : b ≠ c) (h6 : b ≠ m) (h7 : c ≠ m)
    (h8 : ¬(b.sameSide c AL)) (h9 : AL ≠ BC) (h10 : b.onLine AL → False) (h11 : ¬(c.onLine AL)) :
    between b m c := by
  euclid_finish

end Elements.Book1
