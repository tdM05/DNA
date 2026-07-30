import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s4
    (a b c g : Point) (AB : Line)
    (h_g_nsame : ¬g.sameSide c AB) (h_g_nAB : ¬g.onLine AB) (h_c_nAB : ¬c.onLine AB)
    (hassump1 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟)) :
    c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟) := by
  euclid_finish

end Elements.Book1
