import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step3 (a f g h : Point) (ABC ADE : Circle) (AF AG : Line)
  (ha_on_AF : a.onLine AF) (hf_on_AF : f.onLine AF)
  (ha_on_AG : a.onLine AG) (hg_on_AG : g.onLine AG)
  (ha_ABC : a.onCircle ABC) (hf_centre : f.isCentre ABC)
  (hg_in : g.insideCircle ABC) (hga_lt : |(g─a)| < |(f─a)|)
  (hfg : f ≠ g) (hsuppose1 : ¬between f g a)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(f─a)| = |(f─h)|)   -- "that is to say $FH$"
  (hassump2 : |(a─g)| + |(g─f)| > |(f─h)|)   -- "since $AG$ and $GF$ is greater than $FA$, that is to say $FH$ [Prop.~1.20]"
  : |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_apply (line_from_points g f) as GF
  have ha_off : ¬ a.onLine GF := by euclid_finish
  euclid_apply (Elements.Book1.proposition_20 a g f AG GF AF)
  linarith [hassump2]

end Elements.Book3
