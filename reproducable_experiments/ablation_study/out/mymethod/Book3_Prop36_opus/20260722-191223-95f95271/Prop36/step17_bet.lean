import SystemE
import Book3.Prop36.step17_fin
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_bet
  (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (ha_circ : a.onCircle ABC) (hc_circ : c.onCircle ABC)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hbet : between d c a)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
  : between a f c := by
  -- f is the foot of the perpendicular from the centre e to the secant AC, hence inside the
  -- circle; and a,c are the two points where AC meets the circle, so f lies between them.
  have step17_fin : f.insideCircle ABC := by euclid_apply (helper_3_36_step17_fin a c d e f ABC DA EF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between d c a; assumption)) (by euclid_assumption "" (show ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟; assumption)) (by euclid_assumption "" (show e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟); assumption)))
  euclid_apply (circle_line_intersections f a c DA ABC)
  euclid_finish

end Elements.Book3
