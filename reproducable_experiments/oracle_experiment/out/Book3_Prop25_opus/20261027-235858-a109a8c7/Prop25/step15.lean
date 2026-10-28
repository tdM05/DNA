import SystemE
import Book3.Prop09.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_25_step15 (a b c e : Point) (AC : Line) (α : Circle)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC) (hac : a ≠ c)
    (hcentre : e.isCentre α) (haC : a.onCircle α)
    (heq1 : |(a─e)| = |(e─b)|) (heq2 : |(e─b)| = |(e─c)|) :
    b.onCircle α ∧ c.onCircle α := by
  -- Equidistant from centre E ⟹ on the circle; E is then the centre of the completed circle [Prop.~3.9].
  euclid_apply (point_on_circle_if e a b α)
  euclid_apply (point_on_circle_if e a c α)
  euclid_apply (proposition_9 α a b c e)
  euclid_finish

end Elements.Book3
