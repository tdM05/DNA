import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_agh (a f g h : Point) (ABC : Circle)
    (ha_ABC : a.onCircle ABC) (hf_centre : f.isCentre ABC) (h_on_ABC : h.onCircle ABC)
    (hga_lt : |(g─a)| < |(f─a)|) (hg_in_ABC : g.insideCircle ABC)
    (hfg : f ≠ g) (hsuppose1 : ¬between f g a) (h_bet_fgh : between f g h) :
    |(a─g)| > |(g─h)| := by
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points g f) as GF
  have ha_off : ¬a.onLine GF := by euclid_finish
  euclid_apply (Elements.Book1.proposition_20 a g f AG GF AF)
  have tri : |(a─g)| + |(g─f)| > |(a─f)| := by euclid_finish
  have hfa_fh : |(f─a)| = |(f─h)| := by euclid_finish
  have hseg : |(f─h)| = |(f─g)| + |(g─h)| := by euclid_finish
  have e1 : |(a─f)| = |(f─a)| := by euclid_finish
  have e2 : |(g─f)| = |(f─g)| := by euclid_finish
  linarith [tri, hfa_fh, hseg, e1, e2]

end Elements.Book3
