import SystemE
import Book1.Prop31.Main
import Book1.Prop37.step1
import Book1.Prop37.step2
import Book1.Prop37.step3
import Book1.Prop37.step4
import Book1.Prop37.step5
import Book1.Prop37.step6
import Book1.Prop37.step7
import Book1.Prop37.step8
import Book1.Prop37.step9
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_37 : ∀ (a b c d : Point) (AB BC AC BD CD AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d b c BD BC CD ∧ distinctPointsOnLine a d AD ∧
  ¬(AD.intersectsLine BC) ∧ d.sameSide c AB →
  Triangle.area △ a:b:c = Triangle.area △ d:b:c := by
  euclid_intros

  euclid_apply (proposition_31 b a c AC) as BE
  euclid_apply (intersection_lines AD BE) as e
  euclid_apply (proposition_31 c b d BD) as CF
  euclid_apply (intersection_lines AD CF) as f
  have s1 : between d a e ∧ between a d f := by euclid_apply (h_1_37_s1 a b c d e f AB BC AC BD CD AD BE CF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show d ≠ b; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show BD ≠ BC; assumption)) (by (show BC ≠ CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show d.sameSide c AB; assumption)) (by (show b.onLine BE; assumption)) (by (show ¬BE.intersectsLine AC; assumption)) (by (show e.onLine AD; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CF; assumption)) (by (show ¬CF.intersectsLine BD; assumption)) (by (show f.onLine AD; assumption)) (by (show f.onLine CF; assumption)))

  have s2 : b.onLine BE ∧ e.onLine BE ∧ ¬(BE.intersectsLine AC) := by euclid_apply (h_1_37_s2 b e AC BE (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show ¬BE.intersectsLine AC; assumption)))

  have s3 : c.onLine CF ∧ f.onLine CF ∧ ¬(CF.intersectsLine BD) := by euclid_apply (h_1_37_s3 c f BD CF (by (show c.onLine CF; assumption)) (by (show f.onLine CF; assumption)) (by (show ¬CF.intersectsLine BD; assumption)))

  have s4 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF := by euclid_apply (h_1_37_s4 a b c d e f AB BC AC BD CD AD BE CF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show BD ≠ BC; assumption)) (by (show BC ≠ CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show d.sameSide c AB; assumption)) (by (show b.onLine BE; assumption)) (by (show ¬BE.intersectsLine AC; assumption)) (by (show e.onLine AD; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CF; assumption)) (by (show ¬CF.intersectsLine BD; assumption)) (by (show f.onLine AD; assumption)) (by (show f.onLine CF; assumption)) (by (show between d a e ∧ between a d f; assumption)) (by (show b.onLine BE ∧ e.onLine BE ∧ ¬BE.intersectsLine AC; assumption)) (by (show c.onLine CF ∧ f.onLine CF ∧ ¬CF.intersectsLine BD; assumption)))

  have s5_a1 : formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF := by assumption

  have s5 : Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f := by euclid_apply (h_1_37_s5 a b c d e f AB BC AC BD CD AD BE CF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show b.onLine BE; assumption)) (by (show ¬BE.intersectsLine AC; assumption)) (by (show e.onLine AD; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CF; assumption)) (by (show ¬CF.intersectsLine BD; assumption)) (by (show f.onLine AD; assumption)) (by (show f.onLine CF; assumption)) (by (show formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF; assumption)))

  have s6 : Triangle.area △ a:b:c = Triangle.area △ e:a:b := by euclid_apply (h_1_37_s6 a b c d e f AB BC AC BD CD AD BE CF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF; assumption)))

  have s7 : Triangle.area △ d:b:c = Triangle.area △ f:d:c := by euclid_apply (h_1_37_s7 a b c d e f AB BC AC BD CD AD BE CF (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show BD ≠ BC; assumption)) (by (show BC ≠ CD; assumption)) (by (show CD ≠ BD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show ¬AD.intersectsLine BC; assumption)) (by (show d.sameSide c AB; assumption)) (by (show c.onLine CF; assumption)) (by (show ¬CF.intersectsLine BD; assumption)) (by (show f.onLine AD; assumption)) (by (show f.onLine CF; assumption)) (by (show formParallelogram e a b c AD BC BE AC ∧ formParallelogram d f b c AD BC BD CF; assumption)))

  have s8 : Triangle.area △ a:b:c = Triangle.area △ d:b:c := by euclid_apply (h_1_37_s8 a b c d e f (by (show Triangle.area △e:b:a + Triangle.area △a:b:c = Triangle.area △d:b:c + Triangle.area △d:c:f; assumption)) (by (show Triangle.area △ a:b:c = Triangle.area △ e:a:b; assumption)) (by (show Triangle.area △ d:b:c = Triangle.area △ f:d:c; assumption)))

  have s9 : Triangle.area △ a:b:c = Triangle.area △ d:b:c := by euclid_apply (h_1_37_s9 a b c d (by (show Triangle.area △ a:b:c = Triangle.area △ d:b:c; assumption)))

  exact s9

end Elements.Book1
