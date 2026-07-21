import SystemE

namespace Elements.Book1

theorem helper_1_6_step9 (a b c d : Point) (AB BC AC : Line)
    (h1 : between b d a)
    (h2 : ∠ a:b:c = ∠ a:c:b)
    (h3 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a))
    (h4 : a.onLine AB) (h5 : b.onLine AB) (h6 : a ≠ b)
    (h7 : b.onLine BC) (h8 : c.onLine BC)
    (h9 : c.onLine AC) (h10 : a.onLine AC)
    (h11 : AB ≠ BC) (h12 : BC ≠ AC) (h13 : AC ≠ AB) :
    False := by
  euclid_finish

end Elements.Book1
