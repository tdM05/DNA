import SystemE
import Book1.Prop45.step21_bfgl
import Book1.Prop45.step21_bkhm

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step21 (a b c d f g h k l m : Point)
    (FG KH FK GH HM GL LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a7 : g.onLine GH) (a8 : h.onLine GH)
    (a10 : f.sameSide k GH)
    (b1 : h.onLine HM) (b2 : m.onLine HM) (b3 : g.onLine GL) (b4 : l.onLine GL)
    (b7 : m.onLine LM) (b8 : l.onLine LM) (b9 : m ≠ l)
    (b10 : h.sameSide g LM) (b11 : ¬HM.intersectsLine GL) (b12 : ¬GH.intersectsLine LM)
    (hstep9 : k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟))
    (hstep10 : KH = HM)
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (step20 : formParallelogram f l k m FG KH FK LM)
    (hstep21_assumption1 : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d)
    (hstep21_assumption2 : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c)
    : Triangle.area △ f:k:m + Triangle.area △ f:l:m = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  have hlFG : l.onLine FG := hstep18.2.2.1
  have hfl : f ≠ l := hstep18.2.2.2
  have step21_bfgl : between f g l := by euclid_apply (helper_1_45_step21_bfgl f g h k l m FG GH HM GL LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine FG; assumption)) (by euclid_assumption "" (show f ≠ l; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)) (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show g.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m ≠ l; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show ¬HM.intersectsLine GL; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))
  have step21_bkhm : between k h m := by euclid_apply (helper_1_45_step21_bkhm g h k m GH KH HM (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show KH = HM; assumption)) (by euclid_assumption "" (show k.opposingSides m GH ∧ (∠ k:h:g + ∠ g:h:m = ∟ + ∟); assumption)))
  euclid_apply (sum_parallelograms_area f l k m g h FG KH FK LM)
  euclid_finish

end Elements.Book1
