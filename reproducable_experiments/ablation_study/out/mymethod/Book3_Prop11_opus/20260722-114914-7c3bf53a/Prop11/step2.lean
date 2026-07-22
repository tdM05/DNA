import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step2 (a f g : Point) (ABC : Circle) (AF AG : Line)
    (ha_onAF : a.onLine AF) (hf_onAF : f.onLine AF)
    (ha_onAG : a.onLine AG) (hg_onAG : g.onLine AG)
    (ha_on_ABC : a.onCircle ABC) (hf_centre : f.isCentre ABC)
    (hg_inside : g.insideCircle ABC) :
    distinctPointsOnLine a f AF ∧ distinctPointsOnLine a g AG := by
  euclid_finish

end Elements.Book3
