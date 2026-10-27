import SystemE
import Book1.Prop33.Main
import Book1.Prop36.step5_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5 (a b c d e h : Point) (AH BG CD BE CH : Line)
    (ha_AH : a.onLine AH) (hd_AH : d.onLine AH)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hb_BG : b.onLine BG) (hc_BG : c.onLine BG)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD)
    (hh_CH : h.onLine CH) (hc_CH : c.onLine CH)
    (hab_CD : a.sameSide b CD)
    (hpar : ¬AH.intersectsLine BG)
    (hadh : between a d h) (haeh : between a e h) (hdc : d ≠ c)
    (hstep4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH)
    (hstep2 : |(b─c)| = |(e─h)|) :
    |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH) := by
  have step5_ss : e.sameSide b CH := by euclid_apply (helper_1_36_step5_ss a b c d e h AH BG CD CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show between a d h; assumption)) (by euclid_assumption "" (show between a e h; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)))
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
