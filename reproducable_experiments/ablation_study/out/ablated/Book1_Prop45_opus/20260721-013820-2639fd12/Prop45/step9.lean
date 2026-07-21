import SystemE

namespace Elements.Book1

theorem helper_1_45_step9 (g h k m : Point) (GH : Line)
    (h1 : ¬(m.onLine GH)) (h2 : ¬(k.onLine GH)) (h3 : ¬(m.sameSide k GH))
    (h4 : ∠ k:h:g + ∠ g:h:m = ∟ + ∟) :
    k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟) := by
  euclid_finish

end Elements.Book1
