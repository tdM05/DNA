import SystemE
import Book3.Prop36.step28_notDB
import Book3.Prop36.step28_tri
import Book3.Prop36.step28_p47
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28
  (b d e : Point) (ABC : Circle) (EB ED DB : Line)
  (hb : b.onCircle ABC)
  (hbEB : b.onLine EB) (heEB : e.onLine EB)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (hnint : ¬ DB.intersectsCircle ABC)
  (hdni : ¬ d.insideCircle ABC) (hdno : ¬ d.onCircle ABC)
  (step13 : e.isCentre ABC)
  (step28_assumption1 : ∠ e:b:d = ∟)
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  have step28_notDB : ¬ e.onLine DB := by euclid_apply (helper_3_36_step28_notDB e ABC DB (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show ¬ DB.intersectsCircle ABC; assumption)))
  have step28_tri : formTriangle b e d EB ED DB := by euclid_apply (helper_3_36_step28_tri b d e ABC EB ED DB (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show ¬ e.onLine DB; assumption)) (by euclid_assumption "" (show ¬ d.onCircle ABC; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)))
  have step28_p47 : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by euclid_apply (helper_3_36_step28_p47 b d e EB ED DB (by euclid_assumption "" (show formTriangle b e d EB ED DB; assumption)) (by euclid_assumption "" (show ∠ e:b:d = ∟; assumption)))
  exact step28_p47

end Elements.Book3
