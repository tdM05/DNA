import SystemE
import Book1.Prop47.Main
import Book3.Prop36.step8_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step8 (a b d f : Point) (ABC : Circle) (FB DA DB : Line)
  (ha_DA : a.onLine DA) (hf_DA : f.onLine DA) (hd_DA : d.onLine DA)
  (hf_FB : f.onLine FB) (hb_FB : b.onLine FB)
  (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (ha_circ : a.onCircle ABC) (hb_circ : b.onCircle ABC) (hf_centre : f.isCentre ABC)
  (hd_out : ¬ d.onCircle ABC)
  (hnint : ¬DB.intersectsCircle ABC)
  (hfb : distinctPointsOnLine f b FB)
  (step3 : ∠ f:b:d = ∟)
  : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  have step8_tri : formTriangle b f d FB DA DB := by euclid_apply (helper_3_36_step8_tri a b d f ABC FB DA DB (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show f.onLine FB; assumption)) (by euclid_assumption "" (show b.onLine FB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ d.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬DB.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show distinctPointsOnLine f b FB; assumption)))
  euclid_apply (Elements.Book1.proposition_47 b f d FB DA DB ⟨step8_tri, step3⟩)
  euclid_finish

end Elements.Book3
