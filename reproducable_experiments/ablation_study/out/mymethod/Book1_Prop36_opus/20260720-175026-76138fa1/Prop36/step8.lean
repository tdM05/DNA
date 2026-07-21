import SystemE
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hf_BG : f.onLine BG) (hg_BG : g.onLine BG)
    (hb_BG : b.onLine BG) (hc_BG : c.onLine BG)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hh_HG : h.onLine HG) (hg_HG : g.onLine HG) (hhg : h ≠ g)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE)
    (hh_CH : h.onLine CH) (hc_CH : c.onLine CH)
    (hef_ss : e.sameSide f HG)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬EF.intersectsLine HG)
    (hstep5 : |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH)
    (hstep6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_finish

end Elements.Book1
