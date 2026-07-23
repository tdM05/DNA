import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step8_tri (a b d f : Point) (ABC : Circle) (FB DA DB : Line)
  (ha_DA : a.onLine DA) (hf_DA : f.onLine DA) (hd_DA : d.onLine DA)
  (hf_FB : f.onLine FB) (hb_FB : b.onLine FB)
  (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (ha_circ : a.onCircle ABC) (hb_circ : b.onCircle ABC) (hf_centre : f.isCentre ABC)
  (hd_out : ¬ d.onCircle ABC)
  (hnint : ¬DB.intersectsCircle ABC)
  (hfb : distinctPointsOnLine f b FB)
  : formTriangle b f d FB DA DB := by
  have hf_inside : f.insideCircle ABC := by euclid_finish
  have hDA_int : DA.intersectsCircle ABC := by euclid_finish
  have hbnotDA : ¬ b.onLine DA := by
    intro hbDA
    have hdb : d ≠ b := by euclid_finish
    euclid_apply (two_points_determine_line d b DA DB)
    euclid_finish
  euclid_finish

end Elements.Book3
