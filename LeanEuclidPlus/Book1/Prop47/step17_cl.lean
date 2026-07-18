import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step17_cl_par
import Book1.Prop47.step17_cl_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step17_cl
    (a c e l m : Point) (AC CE BC DE AL AE : Line)
    (hmAL : m.onLine AL) (hlAL : l.onLine AL) (haAL : a.onLine AL)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hmBC : m.onLine BC) (hcBC : c.onLine BC)
    (hlDE : l.onLine DE) (heDE : e.onLine DE)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (haAE : a.onLine AE) (heAE : e.onLine AE)
    (hALCE : ¬AL.intersectsLine CE) (hDEBC : ¬DE.intersectsLine BC)
    (haoffCE : ¬a.onLine CE) (hac : a ≠ c)
    (hced : ∠ c:e:d = ∟) (hcelen : |(c─e)| = |(b─c)|) (hec : e ≠ c)
    (heoffAC : ¬e.onLine AC) (hae : a ≠ e) (hle : l ≠ e) (hBCDE : BC ≠ DE) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:c:e + Triangle.area △ a:c:e := by
  have step17_cl_par : formParallelogram m l c e AL CE BC DE := by euclid_apply (helper_1_47_step17_cl_par c e l m AL CE BC DE (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine CE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show l ≠ e; assumption)) (by euclid_assumption "" (show BC ≠ DE; assumption)))
  have step17_cl_tri : formTriangle a c e AC CE AE := by euclid_apply (helper_1_47_step17_cl_tri a c e AC CE AE (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine CE; assumption)) (by euclid_assumption "" (show e.onLine CE; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show ¬a.onLine CE; assumption)) (by euclid_assumption "" (show ¬e.onLine AC; assumption)) (by euclid_assumption "" (show a ≠ c; assumption)) (by euclid_assumption "" (show a ≠ e; assumption)))
  euclid_apply (proposition_41 m c e l a AL CE BC DE AC AE)
  euclid_finish

end Elements.Book1
