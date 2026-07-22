import SystemE
import Book3.Prop11.step_nhout_hin
import Book3.Prop11.step_nhout_h2out
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g h : Point) (ABC ADE : Circle)
    (ha_on_ABC : a.onCircle ABC) (ha_on_ADE : a.onCircle ADE)
    (hnint : ¬ABC.intersectsCircle ADE)
    (hg_inside_ABC : g.insideCircle ABC) (hga_lt : |(g─a)| < |(f─a)|)
    (hf_centre : f.isCentre ABC) (hg_centre : g.isCentre ADE)
    (hfg : f ≠ g) (hsuppose : ¬ between f g a)
    (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (h_nout : ¬h.outsideCircle ADE) :
    False := by
  have step_nhout_hin : h.insideCircle ADE := by euclid_apply (helper_3_11_step_nhout_hin a f g h ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show ¬ between f g a; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)))
  euclid_apply (line_from_points f g) as L
  euclid_apply (center_inside_circle f ABC)
  euclid_apply (intersection_circle_line_extending_points ABC L f g) as h2
  have step_nhout_h2out : h2.outsideCircle ADE := by euclid_apply (helper_3_11_step_nhout_h2out a f g h2 ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show ¬ between f g a; assumption)) (by euclid_assumption "" (show h2.onCircle ABC; assumption)) (by euclid_assumption "" (show between h2 f g; assumption)))
  euclid_apply (intersection_circle_circle_1 h h2 ABC ADE)
  euclid_finish

end Elements.Book3
