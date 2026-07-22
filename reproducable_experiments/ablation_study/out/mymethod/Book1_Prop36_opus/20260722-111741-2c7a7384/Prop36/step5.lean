import SystemE
import Book1.Prop33.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step5 (a b c d e h : Point) (AH BG CD BE CH : Line)
    (haAH : a.onLine AH) (hdAH : d.onLine AH) (heAH : e.onLine AH) (hhAH : h.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD) (hdc : d ≠ c) (hss_ab : a.sameSide b CD)
    (hpar : ¬AH.intersectsLine BG) (hadh : between a d h) (hbaeh : between a e h)
    (step2 : |(b─c)| = |(e─h)|)
    (step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH) :
    |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH) := by
  euclid_apply (proposition_33 e h b c AH BG BE CH)
  euclid_finish

end Elements.Book1
