import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step4_afbe (a b c d e : Point) (AB CD DE BE AF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (haAF : a.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hdscBE : d.sameSide c BE)
    (hcbe : ∠ c:b:e = ∟)
    (hacb : between a c b)
    (hAFCD : ¬AF.intersectsLine CD) (hCDBE : ¬CD.intersectsLine BE)
    (heb : e ≠ b) :
    ¬AF.intersectsLine BE := by
  by_contra h
  euclid_apply (intersection_lines AF BE) as p
  euclid_apply (parallel_line_unique p CD AF BE)
  euclid_finish

end Elements.Book2
