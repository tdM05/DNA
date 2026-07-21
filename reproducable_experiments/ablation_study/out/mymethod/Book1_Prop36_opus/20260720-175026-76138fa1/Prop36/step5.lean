import SystemE
import Book1.Prop33.Main
import Book1.Prop36.step5_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (ha_AH : a.onLine AH) (hd_AH : d.onLine AH) (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hb_BG : b.onLine BG) (hc_BG : c.onLine BG)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD) (hdc : d ≠ c)
    (hab_ss : a.sameSide b CD)
    (he_BE : e.onLine BE) (hb_BE : b.onLine BE)
    (hh_CH : h.onLine CH) (hc_CH : c.onLine CH)
    (hpar : ¬AH.intersectsLine BG) (hpar1 : ¬AB.intersectsLine CD)
    (hbc_eh : |(b─c)| = |(e─h)|)
    (hadh : between a d h) (haeh : between a e h) :
    |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH) := by
  have step5_ss : e.sameSide b CH := by euclid_apply (helper_1_36_step5_ss a b c d e h AH BG AB CD BE CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show between a d h; assumption)) (by euclid_assumption "" (show between a e h; assumption)))
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
