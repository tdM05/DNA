import SystemE
import Book1Variants.Prop35

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (heAH : e.onLine AH) (hhAH : h.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG) (hfBG : f.onLine BG) (hgBG : g.onLine BG)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hhHG : h.onLine HG) (hgHG : g.onLine HG)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hhneg : h ≠ g)
    (hesfHG : e.sameSide f HG)
    (hAHBG : ¬(AH.intersectsLine BG)) (hEFHG : ¬(EF.intersectsLine HG))
    (hstep5 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH))
    (hstep6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_finish

end Elements.Book1
