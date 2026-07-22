import SystemE
import Book1.Prop34.Main
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (heAH : e.onLine AH) (hhAH : h.onLine AH)
    (hfBG : f.onLine BG) (hgBG : g.onLine BG) (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hhHG : h.onLine HG) (hgHG : g.onLine HG)
    (hhg : h ≠ g) (hssef : e.sameSide f HG)
    (hparAHBG : ¬AH.intersectsLine BG) (hparEFHG : ¬EF.intersectsLine HG)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (step6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (line_from_points h f) as HF
  euclid_apply (proposition_34 e h f g AH BG EF HG HF)
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
