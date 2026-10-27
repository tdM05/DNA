import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step9_bad
import Book1.Prop20.step9_da
import Book1.Prop20.step9_iso
import Book1.Prop20.step9_ang
import Book1.Prop20.step9_tri2
import Book1.Prop20.step9_side
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step9_ineq (a b c : Point) (AB BC AC : Line)
    (h : formTriangle a b c AB BC AC) : |(b─a)| + |(a─c)| > |(b─c)| := by
  euclid_apply (extend_point_longer AB b a (c─a)) as d'
  euclid_apply (proposition_3 a d' a c AB AC) as d
  euclid_apply (line_from_points d c) as DC
  have step9_bad : between b a d := by euclid_apply (helper_1_20_step9_bad a b d d' AB (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between b a d'; assumption)) (by euclid_assumption "" (show between a d d'; assumption)))
  have step9_da : |(d─a)| = |(a─c)| := by euclid_apply (helper_1_20_step9_da a c d (by euclid_assumption "" (show |(a─d)| = |(a─c)|; assumption)))
  have step9_iso : ∠ a:d:c = ∠ a:c:d := by euclid_apply (helper_1_20_step9_iso a c d d' AB DC AC (by euclid_assumption "" (show |(d─a)| = |(a─c)|; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show d'.onLine AB; assumption)) (by euclid_assumption "" (show between a d d'; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  have step9_ang : ∠ b:c:d > ∠ a:d:c := by euclid_apply (helper_1_20_step9_ang a b c d AB BC AC DC (by euclid_assumption "" (show ∠ a:d:c = ∠ a:c:d; assumption)) (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  have t_bd : ∠ b:c:d > ∠ b:d:c := by euclid_finish
  have step9_tri2 : formTriangle b c d BC DC AB := by euclid_apply (helper_1_20_step9_tri2 a b c d AB BC DC AC (by euclid_assumption "" (show between b a d; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine DC; assumption)) (by euclid_assumption "" (show d.onLine DC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)))
  have step9_side : |(d─b)| > |(b─c)| := by euclid_apply (helper_1_20_step9_side a b c d AB BC DC (by euclid_assumption "" (show formTriangle b c d BC DC AB; assumption)) (by euclid_assumption "" (show ∠ b:c:d > ∠ b:d:c; assumption)))
  euclid_finish

end Elements.Book1
