import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step9 (a b c d e f : Point) (DE EF DF : Line)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
    (h_d_DF : d.onLine DF) (h_f_DF : f.onLine DF)
    (h_DE_EF : DE ≠ EF) (h_EF_DF : EF ≠ DF) (h_DF_DE : DF ≠ DE)
    (h_ang2 : ∠ b:c:a = ∠ e:f:d) :
    ∠ d:f:e = ∠ b:c:a := by
  have hsymm : ∠ d:f:e = ∠ e:f:d := by euclid_finish
  euclid_finish

end Elements.Book1
