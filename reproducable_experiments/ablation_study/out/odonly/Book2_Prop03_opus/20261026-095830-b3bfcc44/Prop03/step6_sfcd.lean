import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6_sfcd (a b c d e f : Point) (AB CD DE BE AF : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hcAB : c.onLine AB) (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hacb : between a c b)
    (hbcd : ∠ b:c:d = ∟) (hbed : ∠ b:e:d = ∟)
    (hcd_cb : |(c─d)| = |(c─b)|) (hbe_cb : |(b─e)| = |(c─b)|) (hde_cb : |(d─e)| = |(c─b)|)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hAFCD : ¬AF.intersectsLine CD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hCDBE : ¬CD.intersectsLine BE)
    (heb : e ≠ b) :
    a.sameSide f CD := by
  have hnaCD : ¬a.onLine CD := by euclid_finish
  have hnfCD : ¬f.onLine CD := by euclid_finish
  euclid_finish

end Elements.Book2
