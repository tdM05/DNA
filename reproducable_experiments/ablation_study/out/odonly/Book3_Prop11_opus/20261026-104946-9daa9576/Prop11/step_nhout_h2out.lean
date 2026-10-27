import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_h2out (a f g h h2 : Point) (ABC ADE : Circle)
    (ha_ABC : a.onCircle ABC) (hf_centre : f.isCentre ABC) (h_on_ABC : h.onCircle ABC)
    (hh2_ABC : h2.onCircle ABC)
    (hga_lt : |(g─a)| < |(f─a)|)
    (ha_ADE : a.onCircle ADE) (hg_centre : g.isCentre ADE)
    (h_in : h.insideCircle ADE)
    (h_bet_fgh : between f g h) (hh2_bet : between h2 f h) :
    h2.outsideCircle ADE := by
  have hbet2 : between h2 g h := by euclid_finish
  have hlen : |(h2─h)| = |(h2─g)| + |(g─h)| := by euclid_finish
  have hlen2 : |(h2─h)| = |(h2─f)| + |(f─h)| := by euclid_finish
  have hr1 : |(h2─f)| = |(f─a)| := by euclid_finish
  have hr2 : |(f─h)| = |(f─a)| := by euclid_finish
  have hgh : |(g─h)| < |(g─a)| := by euclid_finish
  have e1 : |(g─h2)| = |(h2─g)| := by euclid_finish
  have hgt : |(g─h2)| > |(g─a)| := by
    linarith [hlen, hlen2, hr1, hr2, hgh, hga_lt, e1]
  euclid_finish

end Elements.Book3
