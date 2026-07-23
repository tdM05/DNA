import SystemE
import Book1.Prop16.Main
import Book1.Prop17.Main

namespace Elements.Book1

-- case between m b c → False, via Prop16 (exterior angle) + Prop17 (two angles < 2 right)
theorem bmcC1 (a b c m : Point) (AB BC AC AM : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC) (h6b : a ≠ c)
    (h9 : a.onLine AM) (h10 : m.onLine AM)
    (h18 : m.onLine BC) (h13 : ¬(a.onLine BC)) (h21 : a ≠ m) (h22 : b ≠ m) (h23 : c ≠ m)
    (h12 : ∠ b:a:c = ∟) (hamb : ∠ a:m:b = ∟)
    (h24 : AB ≠ BC) (h25 : BC ≠ AC) (h26 : AC ≠ AB)
    (h27 : AM ≠ BC) (h28 : AM ≠ AB) (h29 : AM ≠ AC)
    (hbet : between m b c) :
    False := by
  euclid_apply (proposition_16 a c b m AC BC AB)
  euclid_apply (proposition_17 a b m AB BC AM)
  euclid_finish

end Elements.Book1
