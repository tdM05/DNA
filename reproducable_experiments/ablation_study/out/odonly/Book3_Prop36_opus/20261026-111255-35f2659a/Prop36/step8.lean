import SystemE
import Book1.Prop47.Main
import Book3.Prop36.step8_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step8 (b d f : Point) (ABC : Circle) (DB DA FB : Line)
  (step2 : distinctPointsOnLine f b FB)
  (hfDA : f.onLine DA) (hdDA : d.onLine DA)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (hfc : f.isCentre ABC) (hbC : b.onCircle ABC)
  (hdin : ¬d.insideCircle ABC) (hdnc : ¬d.onCircle ABC)
  (step3 : ∠ f:b:d = ∟) :
    |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  have step8_tri : formTriangle b f d FB DA DB := by euclid_apply (helper_3_36_step8_tri b d f ABC DB DA FB (by euclid_assumption "" (show distinctPointsOnLine f b FB; assumption)) (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show f.isCentre ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show ∠ f:b:d = ∟; assumption)))
  euclid_apply (Elements.Book1.proposition_47 b f d FB DA DB ⟨step8_tri, step3⟩)
  euclid_finish

end Elements.Book3
