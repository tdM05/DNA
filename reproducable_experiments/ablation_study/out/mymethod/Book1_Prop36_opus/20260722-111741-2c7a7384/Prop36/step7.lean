import SystemE
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step7 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (haAH : a.onLine AH) (hdAH : d.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD) (hdc : d ≠ c) (hss_ab : a.sameSide b CD)
    (hparAHBG : ¬AH.intersectsLine BG) (hparABCD : ¬AB.intersectsLine CD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (step6 : formParallelogram e h b c AH BG BE CH)
    (step7_assumption1 : distinctPointsOnLine b c BG)
    (step7_assumption2 : ¬(BG.intersectsLine AH)) :
    Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
