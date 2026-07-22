import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28_tri
  (b d e : Point) (ABC : Circle) (EB ED DB : Line)
  (hb : b.onCircle ABC)
  (hbEB : b.onLine EB) (heEB : e.onLine EB)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (hnotDB : ¬ e.onLine DB)
  (hdno : ¬ d.onCircle ABC)
  (step13 : e.isCentre ABC)
  : formTriangle b e d EB ED DB := by euclid_finish

end Elements.Book3
