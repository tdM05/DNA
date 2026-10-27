import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step15 (e b c d : Point) (ABC : Circle) (EB EC ED : Line)
    (heEB : e.onLine EB) (hbEB : b.onLine EB)
    (heEC : e.onLine EC) (hcEC : c.onLine EC)
    (heED : e.onLine ED) (hdED : d.onLine ED)
    (hbcirc : b.onCircle ABC) (hccirc : c.onCircle ABC)
    (hecentre : e.isCentre ABC)
    (hdnotin : ¬ d.insideCircle ABC) (hdnotcirc : ¬ d.onCircle ABC) :
    distinctPointsOnLine e b EB ∧ distinctPointsOnLine e c EC ∧ distinctPointsOnLine e d ED := by
  euclid_finish

end Elements.Book3
