import SystemE

namespace Elements.Book1

theorem helper_1_6_step4 (c d : Point) (DC : Line)
    (h1 : d.onLine DC) (h2 : c.onLine DC) :
    d.onLine DC ∧ c.onLine DC := by
  euclid_finish

end Elements.Book1
