import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hALDE_neq
    (b d e : Point) (DE BD CE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (heCE : e.onLine CE) (hBDCE : ¬BD.intersectsLine CE)
    (hdsCE : d.sameSide b CE) (hdBD : d.onLine BD) :
    DE ≠ BD := by
  intro heq
  rw [heq] at heDE
  have hne : BD ≠ CE := by
    intro h; rw [h] at hdBD; euclid_finish
  euclid_apply (intersection_lines_common_point e BD CE)
  euclid_finish

end Elements.Book1
