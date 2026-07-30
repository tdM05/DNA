import SystemE
import Book1.Prop11.step10_foff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s10
    (a b c d e f : Point) (AB : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)

    (hassump1 : ∠ d:c:f = ∠ e:c:f ∧ between d c e)
    : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟ := by
  have s10_x3 : ¬(f.onLine AB) := by euclid_apply (h_1_11_s10_x1 a b c d e f AB (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))
  obtain ⟨hangle_eq, hbetween⟩ := hassump1
  constructor
  · euclid_apply (perpendicular_if d e c f AB)
    euclid_finish
  · euclid_finish

end Elements.Book1
