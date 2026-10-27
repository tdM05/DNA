import SystemE
import Book1.Prop34.Main
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG BE CH EF HG : Line)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hf_BG : f.onLine BG) (hg_BG : g.onLine BG)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hh_HG : h.onLine HG) (hg_HG : g.onLine HG) (hhg : h ≠ g)
    (hef_HG : e.sameSide f HG)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬EF.intersectsLine HG)
    (hstep6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_34 e h b c AH BG BE CH HB)
  euclid_apply (proposition_35' b e h c f g BG AH BE CH EF HG)
  euclid_finish

end Elements.Book1
