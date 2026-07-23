import SystemE

namespace Elements.Book3

theorem helper_3_25_step9 (a b e : Point) (AB : Line)
    (h1 : ∠ a:b:e = ∠ b:a:e)
    (h5 : a.onLine AB) (h6 : b.onLine AB)
    (hab : a ≠ b) (hne : ¬e.onLine AB) (hea : e ≠ a) (heb : e ≠ b) :
    |(e─b)| = |(e─a)| := by
  euclid_finish

end Elements.Book3
