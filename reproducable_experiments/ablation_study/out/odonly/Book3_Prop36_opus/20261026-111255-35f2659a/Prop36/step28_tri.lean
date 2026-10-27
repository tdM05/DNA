import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28_tri (b d e : Point) (ABC : Circle) (DB ED EB : Line)
  (heEB : e.onLine EB) (hbEB : b.onLine EB)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (he : e.isCentre ABC) (hbC : b.onCircle ABC)
  (hdin : ¬d.insideCircle ABC) (hdnc : ¬d.onCircle ABC)
  (hassump1 : ∠ e:b:d = ∟) :
    formTriangle b e d EB ED DB := by
  have hed : e ≠ d := by euclid_finish
  have hbed : ¬ b.onLine ED := by euclid_finish
  euclid_finish

end Elements.Book3
