import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step3_tri (a f g : Point) (ABC : Circle) (AF AG GF : Line)
  (ha_ABC : a.onCircle ABC) (hf_c : f.isCentre ABC) (hg_in : g.insideCircle ABC)
  (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
  (ha_AG : a.onLine AG) (hg_AG : g.onLine AG)
  (hg_GF : g.onLine GF) (hf_GF : f.onLine GF)
  (hfg : f ≠ g)
  (hsuppose1 : ¬ between f g a)
  (hlt : |(g─a)| < |(f─a)|)
  : formTriangle a g f AG GF AF := by
  euclid_finish

end Elements.Book3
