import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step6 (a b c d e h : Point) (AH BG CD BE CH : Line)
    (haAH : a.onLine AH) (hdAH : d.onLine AH) (heAH : e.onLine AH) (hhAH : h.onLine AH)
    (hbBG : b.onLine BG) (hcBG : c.onLine BG)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD) (hdc : d ≠ c) (hss_ab : a.sameSide b CD)
    (hpar : ¬AH.intersectsLine BG) (hadh : between a d h) (hbaeh : between a e h)
    (step5 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH)) :
    formParallelogram e h b c AH BG BE CH := by
  euclid_apply (line_from_points b h) as BH
  euclid_apply (proposition_34 e h b c AH BG BE CH BH)
  euclid_finish

end Elements.Book1
