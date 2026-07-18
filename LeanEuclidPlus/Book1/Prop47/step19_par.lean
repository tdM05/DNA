import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step19_par
    (b c d e : Point) (DE BC BD CE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (heCE : e.onLine CE) (hcCE : c.onLine CE) (hec : e ≠ c)
    (hdbCE : d.sameSide b CE)
    (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE) :
    formParallelogram d e b c DE BC BD CE := by
  euclid_finish

end Elements.Book1
