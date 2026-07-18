import SystemE
import Book1.Prop47.step8_bcAL
import Book1.Prop47.step8_dle
import Book1.Prop47.step18_bmc
import Book1.Prop47.step19_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- BDEC = BL + CL (the square split by ML), and BL = GB (step16), CL = HC (step17).
theorem helper_1_47_step18
    (a b c d e f g h k l m : Point)
    (AB BC BD CE DE AL AC : Line)
    (hbAB : b.onLine AB) (haAB : a.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hmBC : m.onLine BC)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hlDE : l.onLine DE)
    (heCE : e.onLine CE) (hcCE : c.onLine CE)
    (hmAL : m.onLine AL) (hlAL : l.onLine AL) (haAL : a.onLine AL)
    (hbac : ∠ b:a:c = ∟) (hcbd : ∠ c:b:d = ∟)
    (hdaBC : ¬d.sameSide a BC) (hdbCE : d.sameSide b CE)
    (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE)
    (hALBD : ¬AL.intersectsLine BD)
    (hoffBD : ¬a.onLine BD) (haoffBC : ¬a.onLine BC) (hdoffBC : ¬d.onLine BC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hab : a ≠ b) (hbdlen : |(b─d)| = |(b─c)|) (hcelen : |(c─e)| = |(b─c)|)
    (hdelen : |(d─e)| = |(b─c)|) (hec : e ≠ c)
    (hstep16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b)
    (hstep17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by
  have hbc : b ≠ c := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hdl : d ≠ l := by euclid_finish
  have hel : e ≠ l := by euclid_finish
  have hALDE : AL ≠ DE := by euclid_finish
  have hbm : b ≠ m := by euclid_finish
  have hcm : c ≠ m := by euclid_finish
  have hALBC : AL ≠ BC := by euclid_finish
  have step8_bcAL : ¬b.sameSide c AL := by euclid_apply (helper_1_47_step8_bcAL a b c d AL BD BC AB AC (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show ∠ c:b:d = ∟; assumption)) (by euclid_assumption "" (show ¬d.sameSide a BC; assumption)) (by euclid_assumption "" (show ¬d.onLine BC; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)))
  have step8_dle : between d l e := by euclid_apply (helper_1_47_step8_dle a b c d e l AL BD CE DE (by euclid_assumption "" (show a.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬b.sameSide c AL; assumption)) (by euclid_assumption "" (show d ≠ l; assumption)) (by euclid_assumption "" (show e ≠ l; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show AL ≠ DE; assumption)))
  have step18_bmc : between b m c := by euclid_apply (helper_1_47_step18_bmc b c m AL BC (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show AL ≠ BC; assumption)) (by euclid_assumption "" (show b ≠ m; assumption)) (by euclid_assumption "" (show c ≠ m; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show ¬b.sameSide c AL; assumption)))
  have step19_par : formParallelogram d e b c DE BC BD CE := by euclid_apply (helper_1_47_step19_par b c d e DE BC BD CE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  euclid_apply (sum_parallelograms_area d e b c l m DE BC BD CE)
  euclid_finish

end Elements.Book1
