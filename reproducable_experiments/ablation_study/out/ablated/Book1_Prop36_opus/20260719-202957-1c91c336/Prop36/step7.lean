import SystemE
import Book1Variants.Prop35

namespace Elements.Book1

theorem helper_1_36_step7 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (p1 : a.onLine AH) (p2 : d.onLine AH)
    (p5 : b.onLine BG) (p6 : c.onLine BG)
    (p9 : a.onLine AB) (p10 : b.onLine AB) (p11 : d.onLine CD) (p12 : c.onLine CD)
    (p17 : d ≠ c) (p19 : a.sameSide b CD)
    (p21 : ¬(AH.intersectsLine BG)) (p22 : ¬(AB.intersectsLine CD))
    (hstep6 : formParallelogram e h b c AH BG BE CH)
    (hbc : distinctPointsOnLine b c BG) (hpar : ¬(BG.intersectsLine AH)) :
    Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
