import SystemE

namespace Elements.Book3

theorem helper_3_6_step2 (f c : Point) (FC : Line)
    (h1 : f.onLine FC) (h2 : c.onLine FC) :
    f.onLine FC ∧ c.onLine FC := by
  euclid_finish

end Elements.Book3
