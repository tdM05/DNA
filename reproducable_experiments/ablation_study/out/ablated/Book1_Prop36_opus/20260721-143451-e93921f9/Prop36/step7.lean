import SystemE
import Book1Variants.Prop35

namespace Elements.Book1

theorem helper_1_36_step7 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (h1 : a.onLine AH) (h2 : d.onLine AH) (h3 : b.onLine BG) (h4 : c.onLine BG)
    (h5 : a.onLine AB) (h6 : b.onLine AB) (h7 : d.onLine CD) (h8 : c.onLine CD)
    (h9 : d ≠ c) (h10 : a.sameSide b CD) (h11 : ¬(AH.intersectsLine BG)) (h12 : ¬(AB.intersectsLine CD))
    (h13 : formParallelogram e h b c AH BG BE CH)
    (h14 : distinctPointsOnLine b c BG) (h15 : ¬(BG.intersectsLine AH)) :
    Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
