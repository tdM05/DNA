import SystemE
import Book1.Prop33.Main
import Book1.Prop36.step5_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (haAH : a.onLine AH) (hdAH : d.onLine AH) (heAH : e.onLine AH) (hhAH : h.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hdc : d ≠ c)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬AB.intersectsLine CD)
    (hss : a.sameSide b CD)
    (hadh : between a d h) (haeh : between a e h)
    (step2 : |(b─c)| = |(e─h)|)
    (step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH) :
    |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH) := by
  have step5_ss : e.sameSide b CH := by euclid_apply (helper_1_36_step5_ss a b c d e h AH BG AB CD CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show between a d h; assumption)) (by euclid_assumption "" (show between a e h; assumption)))
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
