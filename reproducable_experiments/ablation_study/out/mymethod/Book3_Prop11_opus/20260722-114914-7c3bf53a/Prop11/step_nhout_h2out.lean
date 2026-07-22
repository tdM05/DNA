import SystemE
import Book1.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step_nhout_h2out (a f g h2 : Point) (ABC ADE : Circle)
    (ha_on_ABC : a.onCircle ABC) (ha_on_ADE : a.onCircle ADE)
    (hf_centre : f.isCentre ABC) (hg_centre : g.isCentre ADE)
    (hg_inside_ABC : g.insideCircle ABC) (hga_lt : |(g─a)| < |(f─a)|)
    (hfg : f ≠ g) (hsuppose : ¬ between f g a)
    (h2_on_ABC : h2.onCircle ABC) (h2_bet : between h2 f g) :
    h2.outsideCircle ADE := by
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points g f) as GF
  euclid_apply (line_from_points a f) as AF
  euclid_apply (Elements.Book1.proposition_20 a g f AG GF AF)
  euclid_finish

end Elements.Book3
