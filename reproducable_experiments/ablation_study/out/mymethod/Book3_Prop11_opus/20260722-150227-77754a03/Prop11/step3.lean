import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_11_step3 (a f g h : Point) (ABC ADE : Circle) (AF AG : Line)
  (ha_ABC : a.onCircle ABC) (ha_ADE : a.onCircle ADE)
  (hnint : ¬ ABC.intersectsCircle ADE)
  (hg_in : g.insideCircle ABC)
  (hlt : |(g─a)| < |(f─a)|)
  (hf_c : f.isCentre ABC) (hg_c : g.isCentre ADE)
  (hfg : f ≠ g)
  (hsuppose1 : ¬ between f g a)
  (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
  (hstep2 : distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(f─a)| = |(f─h)|)   -- "that is to say $FH$"
  (hassump2 : |(a─g)| + |(g─f)| > |(f─h)|)   -- "since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]"
  : |(a─g)| > |(f─h)| - |(g─f)| := by
  obtain ⟨haf, hag⟩ := hstep2
  euclid_apply (line_from_points g f) as GF
  -- A, G, F are non-collinear (the reductio config forces it), so they form a triangle.
  have htri : formTriangle a g f AG GF AF := by euclid_finish
  -- Prop 1.20 (triangle inequality) applied to triangle AGF: AG + GF > AF.
  euclid_apply (proposition_20 a g f AG GF AF)
  -- AF = FA = FH (radii of ABC).
  have hsym : |(a─f)| = |(f─a)| := by euclid_finish
  linarith

end Elements.Book3
