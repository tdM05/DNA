import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_h_sym
    (a b c d e f : Point) (AB BC AC DE EF DF : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_ab : a ≠ b)
    (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
    (h_c_AC : c.onLine AC) (h_a_AC : a.onLine AC)
    (h_AB_BC : AB ≠ BC) (h_BC_AC : BC ≠ AC) (h_AC_AB : AC ≠ AB)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_de : d ≠ e)
    (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF)
    (h_f_DF : f.onLine DF) (h_d_DF : d.onLine DF)
    (h_DE_EF : DE ≠ EF) (h_EF_DF : EF ≠ DF) (h_DF_DE : DF ≠ DE)
    (h_ang1 : ∠a:b:c = ∠d:e:f) (h_ang2 : ∠b:c:a = ∠e:f:d)
    (h_bc_ef : |(b─c)| = |(e─f)|)
    (hne : |(a─b)| ≠ |(d─e)|)
    (step1 : |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)|)
    (Hsym : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
      a.onLine AB → b.onLine AB → a ≠ b → b.onLine BC → c.onLine BC →
      c.onLine AC → a.onLine AC → AB ≠ BC → BC ≠ AC → AC ≠ AB →
      d.onLine DE → e.onLine DE → d ≠ e → e.onLine EF → f.onLine EF →
      f.onLine DF → d.onLine DF → DE ≠ EF → EF ≠ DF → DF ≠ DE →
      ∠a:b:c = ∠d:e:f → ∠b:c:a = ∠e:f:d → |(b─c)| = |(e─f)| →
      |(a─b)| ≠ |(d─e)| → (|(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)|) →
      |(a─b)| > |(d─e)| → False)
    (hgt : ¬|(a─b)| > |(d─e)|)
    : False := by
  have hde_gt : |(d─e)| > |(a─b)| := by
    rcases step1 with h | h
    · exact absurd h hgt
    · exact h
  exact Hsym d e f a b c DE EF DF AB BC AC
    h_d_DE h_e_DE h_de h_e_EF h_f_EF h_f_DF h_d_DF h_DE_EF h_EF_DF h_DF_DE
    h_a_AB h_b_AB h_ab h_b_BC h_c_BC h_c_AC h_a_AC h_AB_BC h_BC_AC h_AC_AB
    h_ang1.symm h_ang2.symm h_bc_ef.symm (Ne.symm hne) (Or.symm step1) hde_gt

end Elements.Book1
