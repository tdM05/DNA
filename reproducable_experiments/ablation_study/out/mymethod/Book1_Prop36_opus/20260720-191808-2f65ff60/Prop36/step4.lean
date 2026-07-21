import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step4 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (ha_ah : a.onLine AH) (hd_ah : d.onLine AH)
    (hb_bg : b.onLine BG) (hc_bg : c.onLine BG)
    (he_ah : e.onLine AH) (hh_ah : h.onLine AH)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hd_cd : d.onLine CD) (hc_cd : c.onLine CD)
    (hdc : d ≠ c)
    (hsame : a.sameSide b CD)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬AB.intersectsLine CD)
    (hbdh : between a d h) (hbeh : between a e h)
    (hb_be : b.onLine BE) (he_be : e.onLine BE)
    (hc_ch : c.onLine CH) (hh_ch : h.onLine CH) :
    distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by
  have hne : AH ≠ BG := by euclid_finish
  euclid_finish

end Elements.Book1
