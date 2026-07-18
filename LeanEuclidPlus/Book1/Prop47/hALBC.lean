import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_hALBC
    (a b c d e : Point) (AL BD BC : Line)
    (haAL : a.onLine AL) (hALBD : ¬AL.intersectsLine BD)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hcbd : ∠ c:b:d = ∟)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (haoffBD : ¬a.onLine BD) (haoffBC : ¬a.onLine BC)
    (hbdlen : |(b─d)| = |(b─c)|) (hcelen : |(c─e)| = |(b─c)|) (hec : e ≠ c) :
    AL.intersectsLine BC := by
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hcb : c ≠ b := Ne.symm hbc
  have hBDBC : BD ≠ BC := by euclid_finish
  by_contra hni
  have hALBD_ne : AL ≠ BD := fun h => haoffBD (h ▸ haAL)
  have hboffAL : ¬b.onLine AL := by
    intro hbAL
    euclid_apply (intersection_lines_common_point b AL BD)
    euclid_finish
  euclid_apply (parallel_line_unique b AL BD BC)
  euclid_finish

end Elements.Book1
