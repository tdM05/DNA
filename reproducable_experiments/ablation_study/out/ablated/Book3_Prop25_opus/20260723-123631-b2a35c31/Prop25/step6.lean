import SystemE

namespace Elements.Book3

-- e lies on line AG through a and g; g realizes ∠ g:a:b = ∠ a:b:d (Prop 1.23 construction
-- done in Main).  So ∠ b:a:e = ∠ g:a:b = ∠ a:b:d, and e ≠ a since e is on DB while a is not.
theorem helper_3_25_step6 (a b c d e g : Point) (AC AB AG DB : Line)
    (h1 : a.onLine AG) (h2 : g.onLine AG) (h3 : e.onLine AG)
    (h4 : e.onLine DB) (h5 : d.onLine DB) (h6 : b.onLine DB)
    (h7 : g ≠ a) (h8 : ∠ g:a:b = ∠ a:b:d)
    (h9 : g.onLine AB ∨ g.sameSide d AB)
    (h10 : a.onLine AB) (h11 : b.onLine AB)
    (h12 : a.onLine AC) (h13 : c.onLine AC) (h14 : between a d c)
    (h15 : ¬b.onLine AC) (h16 : a ≠ c) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  euclid_finish

end Elements.Book3
