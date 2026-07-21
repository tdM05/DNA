import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step2_assumption2 (e f g h : Point) (AH BG EF HG : Line)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hf_BG : f.onLine BG) (hg_BG : g.onLine BG)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hh_HG : h.onLine HG) (hg_HG : g.onLine HG) (hhg : h ≠ g)
    (hef_ss : e.sameSide f HG)
    (hpar1 : ¬AH.intersectsLine BG) (hpar2 : ¬EF.intersectsLine HG) :
    |(f─g)| = |(e─h)| := by
  euclid_apply (line_from_points h f) as HF
  euclid_apply (proposition_34 e h f g AH BG EF HG HF)
  euclid_finish

end Elements.Book1
