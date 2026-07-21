import SystemE
import Book1Variants.Prop35

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (p3 : e.onLine AH) (p4 : h.onLine AH)
    (p5 : b.onLine BG) (p6 : c.onLine BG) (p7 : f.onLine BG) (p8 : g.onLine BG)
    (p13 : e.onLine EF) (p14 : f.onLine EF) (p15 : h.onLine HG) (p16 : g.onLine HG)
    (p18 : h ≠ g) (p20 : e.sameSide f HG)
    (p21 : ¬(AH.intersectsLine BG)) (p23 : ¬(EF.intersectsLine HG))
    (p27 : b.onLine BE) (p28 : e.onLine BE) (p29 : c.onLine CH) (p30 : h.onLine CH)
    (hstep6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (proposition_35' f g e h b c BG AH EF HG BE CH)
  euclid_apply (parallelogram_area e h f g AH BG EF HG)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
