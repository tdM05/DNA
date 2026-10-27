import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step3 (a f g h : Point) (ABC ADE : Circle)
    (ha_ABC : a.onCircle ABC) (hf_centre : f.isCentre ABC)
    (hg_in : g.insideCircle ABC) (hfg : f ≠ g)
    (hga_lt : |(g─a)| < |(f─a)|) (hsuppose1 : ¬between f g a)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(f─a)| = |(f─h)|)   -- "that is to say $FH$"
    (hassump2 : |(a─g)| + |(g─f)| > |(f─h)|)   -- "since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]"
    : |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_apply (line_from_points a g) as AG
  euclid_apply (line_from_points g f) as GF
  euclid_apply (line_from_points a f) as AF
  euclid_apply (Elements.Book1.proposition_20 a g f AG GF AF)
  linarith

end Elements.Book3
