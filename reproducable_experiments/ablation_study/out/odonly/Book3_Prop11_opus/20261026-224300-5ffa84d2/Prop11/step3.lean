import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
import Book3.Prop11.step3_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step3 (a f g h : Point) (ABC ADE : Circle) (AF AG : Line)
  (ha_ABC : a.onCircle ABC) (hf_c : f.isCentre ABC) (hg_in : g.insideCircle ABC)
  (ha_ADE : a.onCircle ADE) (hg_c : g.isCentre ADE)
  (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
  (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
  (hfg : f ≠ g)
  (hsuppose1 : ¬ between f g a)
  (hlt : |(g─a)| < |(f─a)|)
  (hassump1 : |(f─a)| = |(f─h)|)
  (hassump2 : |(a─g)| + |(g─f)| > |(f─h)|)
  : |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_apply (line_from_points g f) as GF
  have step3_tri : formTriangle a g f AG GF AF := by euclid_apply (helper_3_11_step3_tri a f g ABC AF AG GF (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show g.insideCircle ABC; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show ¬ between f g a; assumption)) (by euclid_assumption "" (show |(g─a)| < |(f─a)|; assumption)))
  euclid_apply (Elements.Book1.proposition_20 a g f AG GF AF)
  have hkey : |(a─g)| + |(g─f)| > |(f─h)| := by euclid_finish
  linarith [hkey]

end Elements.Book3
