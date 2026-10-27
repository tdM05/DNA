import SystemE
import Book3.Prop11.step_nhout_a
import Book3.Prop11.step_nhout_b
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g h : Point) (ABC ADE : Circle)
    (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
    (hnoint : ¬ABC.intersectsCircle ADE)
    (hg_in : g.insideCircle ABC) (hf_centre : f.isCentre ABC) (hg_centre : g.isCentre ADE)
    (hfg : f ≠ g) (hga_lt : |(g─a)| < |(f─a)|)
    (hsuppose1 : ¬between f g a)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (h_out : ¬h.outsideCircle ADE) :
    False := by
  by_cases h_in : h.insideCircle ADE
  · have step_nhout_a : False := by euclid_apply (helper_3_11_step_nhout_a a f g h ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show h.insideCircle ADE; assumption)))
    exact step_nhout_a
  · have h_on_ADE : h.onCircle ADE := by euclid_finish
    have step_nhout_b : False := by euclid_apply (helper_3_11_step_nhout_b a f g h ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show ¬ABC.intersectsCircle ADE; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show h ≠ a; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show h.onCircle ADE; assumption)))
    exact step_nhout_b

end Elements.Book3
