import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step3 (ABC CDE : Circle) (FEB : Line) (b e f : Point)
    (hb_c : b.onCircle ABC) (he_c : e.onCircle CDE)
    (hf_l : f.onLine FEB) (he_l : e.onLine FEB) (hb_l : b.onLine FEB) :
    b.onCircle ABC ∧ e.onCircle CDE ∧
               f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB := by
  exact ⟨hb_c, he_c, hf_l, he_l, hb_l⟩

end Elements.Book3
