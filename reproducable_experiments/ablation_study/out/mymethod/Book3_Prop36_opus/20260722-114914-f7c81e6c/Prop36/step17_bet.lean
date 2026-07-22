import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_bet
  (a c e f : Point) (ABC : Circle) (DA : Line)
  (ha : a.onCircle ABC) (hc : c.onCircle ABC)
  (haDA : a.onLine DA) (hcDA : c.onLine DA) (hfDA : f.onLine DA)
  (hcentre : e.isCentre ABC)
  (hac : a ≠ c)
  (hlt : |(e─f)| < |(e─a)|)
  : between a f c := by
  euclid_apply (point_in_circle_if e a f ABC)
  euclid_apply (circle_line_intersections f a c DA ABC)
  euclid_finish

end Elements.Book3
