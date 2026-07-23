import SystemE
import Book1.Prop16.Main

namespace Elements.Book1

theorem bmcP16 (a b c m : Point) (AB BC AC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC) (h6b : a ≠ c)
    (h18 : m.onLine BC) (h13 : ¬(a.onLine BC)) (h22 : b ≠ m) (h23 : c ≠ m)
    (h12 : ∠ b:a:c = ∟)
    (h24 : AB ≠ BC) (h25 : BC ≠ AC) (h26 : AC ≠ AB)
    (hbet : between m b c) :
    ∠ a:b:m > ∟ := by
  euclid_apply (proposition_16 a c b m AC BC AB)
  euclid_finish

end Elements.Book1
