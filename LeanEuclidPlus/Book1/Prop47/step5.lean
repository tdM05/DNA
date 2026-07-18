import SystemE
import Book1.Prop14.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step5
    (a b c g : Point) (AB AC AG : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hgAG : g.onLine AG) (haAG : a.onLine AG)
    (hACAB : AC ≠ AB) (hgc : ¬g.sameSide c AB)
    (hstep4 : c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟)) :
    between c a g := by
  obtain ⟨hopp, hsum⟩ := hstep4
  euclid_apply (proposition_14 b a c g AB AC AG)
  euclid_apply (pasch_4 c a g AB AC)
  euclid_finish

end Elements.Book1
