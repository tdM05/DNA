import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step3 (b e f : Point) (ABC CDE : Circle) (FEB : Line)
    (hb : b.onCircle ABC) (he : e.onCircle CDE)
    (hfFEB : f.onLine FEB) (heFEB : e.onLine FEB) (hbFEB : b.onLine FEB) :
    b.onCircle ABC ∧ e.onCircle CDE ∧
               f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB :=
  ⟨hb, he, hfFEB, heFEB, hbFEB⟩

end Elements.Book3
