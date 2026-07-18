import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step8_ecBD
    (b c d e : Point) (DE BC BD CE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (heCE : e.onLine CE) (hcCE : c.onLine CE) (hec : e ≠ c)
    (hdbCE : d.sameSide b CE)
    (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE) :
    e.sameSide c BD := by
  euclid_apply (parallelogram_same_side d e b c DE BC BD CE)
  euclid_finish

end Elements.Book1
