import SystemE
import Book3.Prop11.step_nhout_h2out
import Book3.Prop11.step_nhout_agh
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout (a f g h : Point) (ABC ADE : Circle)
    (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
    (hnoint : ¬ABC.intersectsCircle ADE)
    (hg_in_ABC : g.insideCircle ABC) (hga_lt : |(g─a)| < |(f─a)|)
    (hf_centre : f.isCentre ABC) (hg_centre : g.isCentre ADE)
    (hfg : f ≠ g) (hsuppose1 : ¬between f g a)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (h_nout : ¬h.outsideCircle ADE) :
    False := by
  by_cases h_in : h.insideCircle ADE
  · -- H strictly inside the small circle ADE: show the circles intersect, contradicting hnoint.
    -- H2 = the opposite intersection of line FH with ABC; it is outside ADE, while H is inside it,
    -- so ABC meets ADE.
    euclid_apply (line_from_points f h) as L
    euclid_apply (intersection_circle_line_extending_points ABC L f h) as h2
    have step_nhout_h2out : h2.outsideCircle ADE := by euclid_apply (helper_3_11_step_nhout_h2out a f g h h2 ABC ADE (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show h2.onCircle ABC; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show a.onCircle ADE; assumption)) (by euclid_assumption "" (show g.isCentre ADE; assumption)) (by euclid_assumption "" (show h.insideCircle ADE; assumption)) (by euclid_assumption "" (show between f g h; assumption)) (by euclid_assumption "" (show between h2 f h; assumption)))
    euclid_apply (intersection_circle_circle_1 h h2 ABC ADE)
    euclid_finish
  · -- H on the small circle ADE: the triangle inequality gives |AG| > |GH| = |GA|, impossible
    have h_on_ADE : h.onCircle ADE := by
      by_contra hon
      exact h_nout ⟨h_in, hon⟩
    have step_nhout_agh : |(a─g)| > |(g─h)| := by euclid_apply (helper_3_11_step_nhout_agh a f g h ABC (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show h.onCircle ABC; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show ¬between f g a; assumption)) (by euclid_assumption "" (show between f g h; assumption)))
    euclid_finish

end Elements.Book3
