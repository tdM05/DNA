import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1
open Elements

theorem helper_3_11_step3 (a f g h : Point) (ABC : Circle)
    (h_aABC : a.onCircle ABC) (h_fc : f.isCentre ABC)
    (h_gABC : g.insideCircle ABC) (h_gaLT : |(g─a)| < |(f─a)|)
    (hsuppose1 : ¬between f g a)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(f─a)| = |(f─h)|)   -- "that is to say $FH$"
    (hassump2 : |(a─g)| + |(g─f)| > |(f─h)|)   -- "since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]"
    : |(a─g)| > |(f─h)| - |(g─f)| := by
  -- Honor [Prop.~1.20]: a, g, f are non-collinear in the reductio (all collinear
  -- orders contradict g.insideCircle ABC / |g-a|<|f-a| / ¬between f g a), so triangle
  -- AGF is genuine and the triangle inequality applies.
  euclid_apply (line_from_points g a) as GA
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points g f) as GF
  euclid_apply (proposition_20 g a f GA AF GF)
  have hsym : |(a─f)| = |(f─a)| := by euclid_finish
  linarith

end Elements.Book3
