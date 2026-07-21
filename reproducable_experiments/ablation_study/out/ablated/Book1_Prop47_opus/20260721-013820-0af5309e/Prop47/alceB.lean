import SystemE
import Book1.Prop17.Main

namespace Elements.Book1

-- the Prop17 contradiction: a triangle cannot have two right angles
theorem alceB (p m c : Point) (PM BC PC : Line)
    (h1 : p.onLine PM) (h2 : m.onLine PM)
    (h3 : m.onLine BC) (h4 : c.onLine BC)
    (h5 : p.onLine PC) (h6 : c.onLine PC)
    (h7 : p ≠ m) (h8 : m ≠ c) (h9 : p ≠ c)
    (h10 : PM ≠ BC) (h11 : BC ≠ PC) (h12 : PC ≠ PM)
    (h13 : ∠ p:m:c = ∟) (h14 : ∠ p:c:m = ∟) :
    False := by
  euclid_apply (proposition_17 p m c PM BC PC)
  euclid_finish

end Elements.Book1
