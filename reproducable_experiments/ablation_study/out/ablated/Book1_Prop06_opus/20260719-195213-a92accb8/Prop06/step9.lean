import SystemE

namespace Elements.Book1

theorem helper_1_6_step9 (a b c d : Point) (AB BC AC DC : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC)
    (h6 : c.onLine AC) (h7 : a.onLine AC)
    (h8 : AB ≠ BC) (h9 : BC ≠ AC) (h10 : AC ≠ AB)
    (h11 : between b d a)
    (h12 : d.onLine DC) (h13 : c.onLine DC)
    (h14 : ∠ a:b:c = ∠ a:c:b)
    (h15 : |(d─c)| = |(a─b)| ∧ (∠ b:d:c = ∠ c:a:b) ∧ (∠ b:c:d = ∠ c:b:a)) :
    False := by
  euclid_finish

end Elements.Book1
