import SystemE

namespace Elements.Book3

theorem helper_3_25_step6 (a b d e g : Point) (AB AG : Line)
    (h1 : ∠ g:a:b = ∠ a:b:d) (h2 : g ≠ a) (h3 : ¬g.onLine AB)
    (h4 : a.onLine AG) (h5 : g.onLine AG) (h6 : e.onLine AG)
    (h7 : a.onLine AB) (h8 : b.onLine AB)
    (h9 : ¬between e a g) (h10 : e ≠ a) (hab : a ≠ b) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  euclid_finish

end Elements.Book3
