import SystemE

set_option systemE.solverTime 120

namespace Elements.Book2

-- F = (line AF ∩ line DE).  E lies on the B-side of the side CD (E,B on BE, BE ∥ CD so CD cannot
-- separate them), F on the A-side (F,A on AF, AF ∥ CD), and A,B are on opposite sides of CD
-- because C lies between them on AB and C ∈ CD.  Hence E,F are on opposite sides of CD and
-- D (= CD ∩ DE) is between them on DE.
theorem helper_2_3_step2 (a b c d e f : Point) (AB DE CD BE AF : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : c.onLine AB) (h4 : a ≠ b)
    (h5 : between a c b)
    (h6 : d.onLine DE) (h7 : e.onLine DE) (h8 : f.onLine DE)
    (h9 : a.onLine AF) (h10 : f.onLine AF)
    (h11 : d.onLine CD) (h12 : c.onLine CD)
    (h13 : e.onLine BE) (h14 : b.onLine BE) (h15 : e ≠ b)
    (h16 : ¬(AF.intersectsLine CD)) (h17 : ¬(CD.intersectsLine BE))
    (h18 : ¬(DE.intersectsLine AB))
    (h19 : |(d─e)| = |(c─b)|) (h20 : |(c─d)| = |(c─b)|) (h21 : |(b─e)| = |(c─b)|)
    (h22 : ∠ b:c:d = ∟) (h23 : d.sameSide c BE) :
    f.onLine DE ∧ between e d f := by
  have hcd : c ≠ d := by euclid_finish
  have hnab : ¬(a.sameSide b CD) := by euclid_finish
  have hne : e.sameSide b CD := by euclid_finish
  have hnf : f.sameSide a CD := by euclid_finish
  have href : ¬(e.sameSide f CD) := by euclid_finish
  have hedf : between e d f := by
    euclid_apply (pasch_4 e d f CD DE)
    euclid_finish
  euclid_finish

end Elements.Book2
