import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_6_step3 (b e f : Point) (ABC CDE : Circle) (FEB : Line)
    (hb_ABC : b.onCircle ABC) (he_CDE : e.onCircle CDE)
    (hf_FEB : f.onLine FEB) (he_FEB : e.onLine FEB) (hb_FEB : b.onLine FEB) :
    b.onCircle ABC ∧ e.onCircle CDE ∧
               f.onLine FEB ∧ e.onLine FEB ∧ b.onLine FEB := by
  exact ⟨hb_ABC, he_CDE, hf_FEB, he_FEB, hb_FEB⟩

end Elements.Book3
