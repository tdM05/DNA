import SystemE
import Book1Variants.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step2_assumption2 (e f g h : Point) (AH BG EF HG : Line)
    (he_ah : e.onLine AH) (hh_ah : h.onLine AH)
    (hf_bg : f.onLine BG) (hg_bg : g.onLine BG)
    (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
    (hh_hg : h.onLine HG) (hg_hg : g.onLine HG)
    (hhg : h ≠ g)
    (hsame : e.sameSide f HG)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬EF.intersectsLine HG) :
    |(f─g)| = |(e─h)| := by
  euclid_apply (proposition_34' e h f g AH BG EF HG)
  euclid_finish

end Elements.Book1
