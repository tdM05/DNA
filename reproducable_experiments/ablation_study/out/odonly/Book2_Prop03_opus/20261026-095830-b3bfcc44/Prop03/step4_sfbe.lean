import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_sfbe (a b c d e f : Point) (AB CD DE BE AF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcbe : ∠ c:b:e = ∟)
    (hacb : between a c b)
    (hAFBE : ¬AF.intersectsLine BE)
    (heb : e ≠ b) :
    a.sameSide f BE := by
  have hnaBE : ¬a.onLine BE := by euclid_finish
  have hnfBE : ¬f.onLine BE := by euclid_finish
  euclid_finish

end Elements.Book2
