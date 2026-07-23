import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28_tri (b d e : Point) (ABC : Circle) (EB ED DB : Line)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB)
  (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (he_centre : e.isCentre ABC) (hb_circ : b.onCircle ABC)
  (hd_notinside : ¬ d.insideCircle ABC) (hd_noncircle : ¬ d.onCircle ABC)
  (htangent : ¬ DB.intersectsCircle ABC)
  : formTriangle b e d EB ED DB := by
  have hne_DB : ¬ e.onLine DB := by euclid_finish
  have hbe : b ≠ e := by euclid_finish
  have hed : e ≠ d := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  euclid_finish

end Elements.Book3
