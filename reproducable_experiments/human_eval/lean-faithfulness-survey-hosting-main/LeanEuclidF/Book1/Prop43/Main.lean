import SystemE
import Book1.Prop43.step1
import Book1.Prop43.step2
import Book1.Prop43.step3
import Book1.Prop43.step4
import Book1.Prop43.step5
import Book1.Prop43.step6
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_43 : ∀ (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line),
  formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC ∧ k.onLine AC ∧
  between a h d ∧ formParallelogram a h e k AD EF AB GH ∧ formParallelogram k f g c EF BC GH CD →
  (Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d) := by
  euclid_intros

  have s1_a1 : formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC := by euclid_finish

  have s1 : Triangle.area △ a:b:c = Triangle.area △ a:c:d := by euclid_apply (h_1_43_s1 a b c d AD BC AB CD AC (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show formParallelogram a d b c AD BC AB CD ∧ distinctPointsOnLine a c AC; assumption)))

  have s2_a1 : formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC := by euclid_finish

  have s2 : Triangle.area △ a:e:k = Triangle.area △ a:h:k := by euclid_apply (h_1_43_s2 a e k h AD EF AB GH AC (by (show a.onLine AD; assumption)) (by (show h.onLine AD; assumption)) (by (show e.onLine EF; assumption)) (by (show k.onLine EF; assumption)) (by (show a.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show h.onLine GH; assumption)) (by (show k.onLine GH; assumption)) (by (show h ≠ k; assumption)) (by (show a.sameSide e GH; assumption)) (by (show ¬AD.intersectsLine EF; assumption)) (by (show ¬AB.intersectsLine GH; assumption)) (by (show formParallelogram a h e k AD EF AB GH ∧ distinctPointsOnLine a k AC; assumption)))

  have s3 : Triangle.area △ k:f:c = Triangle.area △ k:g:c := by euclid_apply (h_1_43_s3 k f g c EF BC GH CD AC (by (show k.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show k.onLine GH; assumption)) (by (show g.onLine GH; assumption)) (by (show f.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show f ≠ c; assumption)) (by (show k.sameSide g CD; assumption)) (by (show ¬EF.intersectsLine BC; assumption)) (by (show ¬GH.intersectsLine CD; assumption)) (by (show k.onLine AC; assumption)) (by (show c.onLine AC; assumption)))

  have s4_a1 : Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c := by euclid_finish

  have s4 : Triangle.area △ a:e:k + Triangle.area △ k:g:c = Triangle.area △ a:h:k + Triangle.area △ k:f:c := by euclid_apply (h_1_43_s4 a e k g h f c (by (show Triangle.area △ a:e:k = Triangle.area △ a:h:k ∧ Triangle.area △ k:f:c = Triangle.area △ k:g:c; assumption)) (by (show Triangle.area △ a:e:k = Triangle.area △ a:h:k; assumption)) (by (show Triangle.area △ k:f:c = Triangle.area △ k:g:c; assumption)))

  have s5 : Triangle.area △ a:b:c = Triangle.area △ a:d:c := by euclid_apply (h_1_43_s5 a b c d (by (show Triangle.area △ a:b:c = Triangle.area △ a:c:d; assumption)))

  have s6 : Triangle.area △ e:b:g + Triangle.area △ e:g:k = Triangle.area △ h:k:f + Triangle.area △ h:f:d := by euclid_apply (h_1_43_s6 a b c d e f g h k AD BC AB CD AC EF GH (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show h.onLine AD; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show g.onLine BC; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show f.onLine CD; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show k.onLine AC; assumption)) (by (show e.onLine EF; assumption)) (by (show k.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show h.onLine GH; assumption)) (by (show k.onLine GH; assumption)) (by (show g.onLine GH; assumption)) (by (show d ≠ c; assumption)) (by (show a ≠ c; assumption)) (by (show h ≠ k; assumption)) (by (show f ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show a.sameSide e GH; assumption)) (by (show k.sameSide g CD; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show ¬AD.intersectsLine EF; assumption)) (by (show ¬AB.intersectsLine GH; assumption)) (by (show ¬EF.intersectsLine BC; assumption)) (by (show ¬GH.intersectsLine CD; assumption)) (by (show between a h d; assumption)) (by (show Triangle.area △ a:e:k + Triangle.area △ k:g:c = Triangle.area △ a:h:k + Triangle.area △ k:f:c; assumption)) (by (show Triangle.area △ a:b:c = Triangle.area △ a:d:c; assumption)))

  exact s6

end Elements.Book1
