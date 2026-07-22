import SystemE
import Book1Variants.Prop35

namespace Elements.Book1

theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (h1 : e.onLine AH) (h2 : h.onLine AH) (h3 : f.onLine BG) (h4 : g.onLine BG)
    (h5 : e.onLine EF) (h6 : f.onLine EF) (h7 : h.onLine HG) (h8 : g.onLine HG)
    (h9 : h ≠ g) (h10 : e.sameSide f HG) (h11 : ¬(AH.intersectsLine BG)) (h12 : ¬(EF.intersectsLine HG))
    (h13 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (parallelogram_same_side e h f g AH BG EF HG)
  euclid_apply (parallelogram_same_side e h b c AH BG BE CH)
  euclid_apply (proposition_35' g h e f c b BG AH HG EF CH BE)
  euclid_apply (parallelogram_area e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
