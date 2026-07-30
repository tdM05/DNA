import SystemE
import Book1.Prop35.step1
import Book1.Prop35.step2
import Book1.Prop35.step3
import Book1.Prop35.step4
import Book1.Prop35.step5
import Book1.Prop35.step6
import Book1.Prop35.step7
import Book1.Prop35.step8
import Book1.Prop35.step9
import Book1.Prop35.step10
import Book1.Prop35.step11
import Book1.Prop35.step12
import Book1.Prop35.step13
import Book1.Prop35.step14
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_35 : ∀ (a b c d e f g : Point) (AF BC AB CD EB FC : Line),
  formParallelogram a d b c AF BC AB CD ∧ formParallelogram e f b c AF BC EB FC ∧
  between a d e ∧ between d e f ∧ g.onLine CD ∧ g.onLine EB →
  Triangle.area △a:b:d + Triangle.area △d:b:c = Triangle.area △e:b:c + Triangle.area △ e:c:f := by
  euclid_intros

  have s1_a1 : formParallelogram a d b c AF BC AB CD := by euclid_finish

  have s1 : |(a─d)| = |(b─c)| := by euclid_apply (h_1_35_s1 a d b c AF BC AB CD (by (show formParallelogram a d b c AF BC AB CD; assumption)))

  have s2 : |(e─f)| = |(b─c)| := by euclid_apply (h_1_35_s2 e f b c AF BC EB FC (by (show e.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show e.onLine EB; assumption)) (by (show b.onLine EB; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show f ≠ c; assumption)) (by (show e.sameSide b FC; assumption)) (by (show ¬AF.intersectsLine BC; assumption)) (by (show ¬EB.intersectsLine FC; assumption)))

  have s3 : |(a─d)| = |(e─f)| := by euclid_apply (h_1_35_s3 a d e f b c (by (show |(a─d)| = |(b─c)|; assumption)) (by (show |(e─f)| = |(b─c)|; assumption)))

  have s4 : distinctPointsOnLine d e AF := by euclid_apply (h_1_35_s4 a d e AF (by (show d.onLine AF; assumption)) (by (show e.onLine AF; assumption)) (by (show between a d e; assumption)))

  have s5 : |(a─e)| = |(d─f)| := by euclid_apply (h_1_35_s5 a d e f (by (show between a d e; assumption)) (by (show between d e f; assumption)) (by (show |(a─d)| = |(e─f)|; assumption)))

  have s6 : |(a─b)| = |(d─c)| := by euclid_apply (h_1_35_s6 a d b c AF BC AB CD (by (show formParallelogram a d b c AF BC AB CD; assumption)))

  have s7 : |(e─a)| = |(f─d)| ∧ |(a─b)| = |(d─c)| := by euclid_apply (h_1_35_s7 a d e f b c (by (show |(a─e)| = |(d─f)|; assumption)) (by (show |(a─b)| = |(d─c)|; assumption)))

  have s8 : ∠ f:d:c = ∠ e:a:b := by euclid_apply (h_1_35_s8 a d e f b c AF BC AB CD (by (show formParallelogram a d b c AF BC AB CD; assumption)) (by (show f.onLine AF; assumption)) (by (show e.onLine AF; assumption)) (by (show between a d e; assumption)) (by (show between d e f; assumption)))

  have s9 : |(e─b)| = |(f─c)| := by euclid_apply (h_1_35_s9 a d e f b c AF BC AB CD EB FC (by (show formParallelogram a d b c AF BC AB CD; assumption)) (by (show e.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show e.onLine EB; assumption)) (by (show b.onLine EB; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between a d e; assumption)) (by (show between d e f; assumption)) (by (show ¬EB.intersectsLine FC; assumption)) (by (show e.sameSide b FC; assumption)) (by (show |(a─e)| = |(d─f)|; assumption)) (by (show |(a─b)| = |(d─c)|; assumption)) (by (show ∠ f:d:c = ∠ e:a:b; assumption)))

  have s10 : Triangle.area △ e:a:b = Triangle.area △ d:f:c := by euclid_apply (h_1_35_s10 a d e f b c AF BC AB CD EB FC (by (show formParallelogram a d b c AF BC AB CD; assumption)) (by (show e.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show e.onLine EB; assumption)) (by (show b.onLine EB; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show between a d e; assumption)) (by (show between d e f; assumption)) (by (show ¬EB.intersectsLine FC; assumption)) (by (show e.sameSide b FC; assumption)) (by (show |(a─e)| = |(d─f)|; assumption)) (by (show |(a─b)| = |(d─c)|; assumption)) (by (show ∠ f:d:c = ∠ e:a:b; assumption)) (by (show |(e─b)| = |(f─c)|; assumption)))

  have s11 : Triangle.area △ e:a:b - Triangle.area △ d:g:e = Triangle.area △ d:f:c - Triangle.area △ d:g:e := by euclid_apply (h_1_35_s11 e a b d g f c (by (show Triangle.area △ e:a:b = Triangle.area △ d:f:c; assumption)))

  have s12 : Triangle.area △ a:b:d + Triangle.area △ b:g:d = Triangle.area △ e:g:c + Triangle.area △ e:c:f := by euclid_apply (h_1_35_s12 a d e f b c g AF BC AB CD EB FC (by (show formParallelogram a d b c AF BC AB CD; assumption)) (by (show e.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show e.onLine EB; assumption)) (by (show b.onLine EB; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show g.onLine CD; assumption)) (by (show g.onLine EB; assumption)) (by (show between a d e; assumption)) (by (show between d e f; assumption)) (by (show ¬EB.intersectsLine FC; assumption)) (by (show e.sameSide b FC; assumption)) (by (show f ≠ c; assumption)) (by (show Triangle.area △ e:a:b - Triangle.area △ d:g:e = Triangle.area △ d:f:c - Triangle.area △ d:g:e; assumption)))

  have s13 : Triangle.area △ a:b:d + Triangle.area △ b:g:d + Triangle.area △ g:b:c =
              Triangle.area △ e:g:c + Triangle.area △ e:c:f + Triangle.area △ g:b:c := by euclid_apply (h_1_35_s13 a b c d e f g (by (show Triangle.area △ a:b:d + Triangle.area △ b:g:d = Triangle.area △ e:g:c + Triangle.area △ e:c:f; assumption)))

  have s14 : Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:b:c + Triangle.area △ e:c:f := by euclid_apply (h_1_35_s14 a d e f b c g AF BC AB CD EB FC (by (show formParallelogram a d b c AF BC AB CD; assumption)) (by (show e.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show e.onLine EB; assumption)) (by (show b.onLine EB; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show g.onLine CD; assumption)) (by (show g.onLine EB; assumption)) (by (show between a d e; assumption)) (by (show between d e f; assumption)) (by (show ¬EB.intersectsLine FC; assumption)) (by (show e.sameSide b FC; assumption)) (by (show f ≠ c; assumption)) (by (show Triangle.area △ a:b:d + Triangle.area △ b:g:d + Triangle.area △ g:b:c = Triangle.area △ e:g:c + Triangle.area △ e:c:f + Triangle.area △ g:b:c; assumption)))

  exact s14

end Elements.Book1
