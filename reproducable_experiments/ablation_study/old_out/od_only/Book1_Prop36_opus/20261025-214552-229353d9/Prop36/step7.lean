import SystemE
import Book1Variants.Prop35

namespace Elements.Book1

theorem helper_1_36_step7 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (haAH : a.onLine AH) (hdAH : d.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD) (hdnec : d ≠ c)
    (hasbCD : a.sameSide b CD)
    (hAHBG : ¬(AH.intersectsLine BG)) (hABCD : ¬(AB.intersectsLine CD))
    (hbcBG : distinctPointsOnLine b c BG)
    (hBGAH : ¬(BG.intersectsLine AH))
    (hstep6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_finish

end Elements.Book1
