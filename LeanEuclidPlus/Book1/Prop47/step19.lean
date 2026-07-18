import SystemE
import Book1.Prop47.step19_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step19
    (b c d e : Point) (DE BC BD CE : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hdBD : d.onLine BD) (hbBD : b.onLine BD)
    (heCE : e.onLine CE) (hcCE : c.onLine CE) (hec : e ≠ c)
    (hdbCE : d.sameSide b CE)
    (hDEBC : ¬DE.intersectsLine BC) (hBDCE : ¬BD.intersectsLine CE)
    (hcbd : ∠ c:b:d = ∟) (hdelen : |(d─e)| = |(b─c)|) (hbdlen : |(b─d)| = |(b─c)|) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)| := by
  have step19_par : formParallelogram d e b c DE BC BD CE := by euclid_apply (helper_1_47_step19_par b c d e DE BC BD CE (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)) (by euclid_assumption "" (show d.sameSide b CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show ¬BD.intersectsLine CE; assumption)))
  euclid_apply (rectangle_area d e b c DE BC BD CE)
  euclid_finish

end Elements.Book1
