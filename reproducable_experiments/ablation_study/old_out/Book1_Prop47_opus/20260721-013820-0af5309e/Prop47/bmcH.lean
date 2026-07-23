import SystemE

namespace Elements.Book1

-- does ∠amc=∟ follow from ∠amb=∟ + collinearity of b,m,c ?
theorem bmcH (a b c m : Point) (BC AL : Line)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c) (h18 : m.onLine BC)
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h13 : ¬(a.onLine BC))
    (h21 : a ≠ m) (h22 : b ≠ m) (h23 : c ≠ m)
    (hamb : ∠ a:m:b = ∟) :
    ∠ a:m:c = ∟ := by
  euclid_finish

end Elements.Book1
