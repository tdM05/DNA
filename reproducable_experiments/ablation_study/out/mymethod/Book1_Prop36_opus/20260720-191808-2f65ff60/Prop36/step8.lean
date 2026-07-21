import SystemE
import Book1Variants.Prop34
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- EFGH equal to EBCH [Prop.~1.34]: same base EH, same parallels.  Same reasoning
-- as step7; the diagonal triangulations of EBCH agree (parallelogram_area).
theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (he_ah : e.onLine AH) (hh_ah : h.onLine AH)
    (hb_bg : b.onLine BG) (hc_bg : c.onLine BG) (hf_bg : f.onLine BG) (hg_bg : g.onLine BG)
    (he_ef : e.onLine EF) (hf_ef : f.onLine EF)
    (hh_hg : h.onLine HG) (hg_hg : g.onLine HG)
    (hhg : h ≠ g)
    (hsame_hg : e.sameSide f HG)
    (hpar : ¬AH.intersectsLine BG) (hpar3 : ¬EF.intersectsLine HG)
    (hstep6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (proposition_34' e h f g AH BG EF HG)
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
