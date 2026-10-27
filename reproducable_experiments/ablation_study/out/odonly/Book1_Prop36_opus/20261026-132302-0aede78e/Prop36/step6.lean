import SystemE
import Book1.Prop36.step5_ss
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step6 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (left_1 : a.onLine AH) (left_2 : d.onLine AH)
    (left_11p : e.onLine AH) (left_12 : h.onLine AH)
    (left_3 : b.onLine BG) (left_4 : c.onLine BG)
    (left_5 : a.onLine AB) (left_6 : b.onLine AB)
    (left_8p : d.onLine CD) (left_9 : c.onLine CD) (right_9 : d ≠ c)
    (left_8 : a.sameSide b CD) (left_10 : ¬AH.intersectsLine BG) (right_10 : ¬AB.intersectsLine CD)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (left_21 : between a d h) (right_21 : between a e h)
    (step4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH)
    (step5 : |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH) :
    formParallelogram e h b c AH BG BE CH := by
  have step5_ss : e.sameSide b CH := by euclid_apply (helper_1_36_step5_ss a b c d e h AH BG AB CD CH (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show d.onLine AH; assumption)) (by euclid_assumption "" (show e.onLine AH; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show b.onLine BG; assumption)) (by euclid_assumption "" (show c.onLine BG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d ≠ c; assumption)) (by euclid_assumption "" (show a.sameSide b CD; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine BG; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine CD; assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show between a d h; assumption)) (by euclid_assumption "" (show between a e h; assumption)))
  euclid_finish

end Elements.Book1
