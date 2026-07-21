import SystemE
import Book1.Prop33.Main
import Book1.Prop36.step5_ss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (ha_ah : a.onLine AH) (hd_ah : d.onLine AH) (he_ah : e.onLine AH) (hh_ah : h.onLine AH)
    (hb_bg : b.onLine BG) (hc_bg : c.onLine BG)
    (he_be : e.onLine BE) (hb_be : b.onLine BE)
    (hh_ch : h.onLine CH) (hc_ch : c.onLine CH)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hd_cd : d.onLine CD) (hc_cd : c.onLine CD)
    (hdc : d ≠ c)
    (hsame_cd : a.sameSide b CD)
    (hadh : between a d h) (hbeh : between a e h)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬AB.intersectsLine CD)
    (hlen : |(b─c)| = |(e─h)|)
    (hstep4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH) :
    |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH) := by
  obtain ⟨hdist_eb, hdist_hc⟩ := hstep4
  have step5_ss : e.sameSide b CH := by euclid_apply (helper_1_36_step5_ss a b c d e h AH BG AB CD CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show between a d h; assumption)) (by euclid_assumption "" (show between a e h; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)))
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
