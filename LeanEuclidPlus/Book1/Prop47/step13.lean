import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step13_par
import Book1.Prop47.step13_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step13
    (a b c d e l m : Point) (AB BC BD DE AL AD : Line)
    (hmAL : m.onLine AL) (hlAL : l.onLine AL) (haAL : a.onLine AL)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hmBC : m.onLine BC) (hbBC : b.onLine BC)
    (hlDE : l.onLine DE) (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hALBD : ¬AL.intersectsLine BD) (hDEBC : ¬DE.intersectsLine BC)
    (hoffBD : ¬a.onLine BD) (hab : a ≠ b)
    (hbde : ∠ b:d:e = ∟) (hbdlen : |(b─d)| = |(b─c)|)
    (hce_len : |(c─e)| = |(b─c)|) (hec : e ≠ c) (hdelen : |(d─e)| = |(b─c)|)
    (hassump1 : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL)) :
    Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d := by
  have hbc : b ≠ c := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have had : a ≠ d := by euclid_finish
  have hdoffAB : ¬d.onLine AB := by euclid_finish
  have hld : l ≠ d := by euclid_finish
  have hbDE : ¬b.onLine DE := by euclid_finish
  have hBCDE : BC ≠ DE := by euclid_finish
  have step13_par : formParallelogram m l b d AL BD BC DE := by euclid_apply (helper_1_47_step13_par b d l m AL BD BC DE (by euclid_assumption "" (show m.onLine AL; assumption)) (by euclid_assumption "" (show l.onLine AL; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show m.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show l.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show ¬AL.intersectsLine BD; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine BC; assumption)) (by euclid_assumption "" (show l ≠ d; assumption)) (by euclid_assumption "" (show BC ≠ DE; assumption)))
  have step13_tri : formTriangle a b d AB BD AD := by euclid_apply (helper_1_47_step13_tri a b d AB BD AD (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬d.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)))
  euclid_apply (proposition_41 m b d l a AL BD BC DE AB AD)
  euclid_finish

end Elements.Book1
