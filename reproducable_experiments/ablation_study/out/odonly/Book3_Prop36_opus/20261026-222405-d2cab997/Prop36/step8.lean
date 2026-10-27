import SystemE
import Book1.Prop47.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step8 (f b d : Point) (ABC : Circle) (FB DA DB : Line)
    (hbFB : b.onLine FB) (hfFB : f.onLine FB)
    (hfDA : f.onLine DA) (hdDA : d.onLine DA)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB)
    (hbcirc : b.onCircle ABC) (hfcenter : f.isCentre ABC)
    (hdnotcirc : ¬ d.onCircle ABC) (hdnotin : ¬ d.insideCircle ABC)
    (hangle : ∠ f:b:d = ∟) :
    |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  euclid_apply (proposition_47 b f d FB DA DB)
  euclid_finish

end Elements.Book3
