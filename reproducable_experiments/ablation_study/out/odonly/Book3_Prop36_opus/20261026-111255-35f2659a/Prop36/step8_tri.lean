import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step8_tri (b d f : Point) (ABC : Circle) (DB DA FB : Line)
  (step2 : distinctPointsOnLine f b FB)
  (hfDA : f.onLine DA) (hdDA : d.onLine DA)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (hfc : f.isCentre ABC) (hbC : b.onCircle ABC)
  (hdin : ¬d.insideCircle ABC) (hdnc : ¬d.onCircle ABC)
  (step3 : ∠ f:b:d = ∟) :
    formTriangle b f d FB DA DB := by
  have hfd : f ≠ d := by euclid_finish
  have hboff : ¬ b.onLine DA := by euclid_finish
  euclid_finish

end Elements.Book3
