import SystemE
import Book1.Prop32.Main

namespace Elements.Book1

theorem bmcP32 (a b c m : Point) (AB BC AM : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h9 : a.onLine AM) (h10 : m.onLine AM)
    (h18 : m.onLine BC) (h13 : ¬(a.onLine BC)) (h21 : a ≠ m) (h22 : b ≠ m) (h23 : c ≠ m)
    (h24 : AB ≠ BC) (h27 : AM ≠ BC) (h28 : AM ≠ AB)
    (hbet : between m b c) :
    ∠ a:m:b + ∠ m:b:a + ∠ b:a:m = ∟ + ∟ := by
  euclid_apply (proposition_32 a m b c AM BC AB)
  euclid_finish

end Elements.Book1
