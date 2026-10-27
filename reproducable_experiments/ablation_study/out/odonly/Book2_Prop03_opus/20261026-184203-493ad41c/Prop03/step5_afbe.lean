import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step5_afbe (a b c d e f : Point) (AB DE CD AF BE : Line)
    (h_acb : between a c b)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB) (h_c_AB : c.onLine AB)
    (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_f_DE : f.onLine DE)
    (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD)
    (h_a_AF : a.onLine AF) (h_f_AF : f.onLine AF)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (h_e_BE : e.onLine BE) (h_b_BE : b.onLine BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (h_dsc_BE : d.sameSide c BE) (h_eb : e ≠ b) :
    ¬(AF.intersectsLine BE) := by
  by_contra h_int
  euclid_apply (intersection_lines AF BE) as p
  euclid_apply (parallel_line_unique p CD AF BE)
  euclid_finish

end Elements.Book2
