import SystemE
import Book1.Prop31.Main
import Book1.Prop40.step1
import Book1.Prop40.step3
import Book1.Prop40.step4
import Book1.Prop40.step5
import Book1.Prop40.step6
import Book1.Prop40.step7
import Book1.Prop40.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_40 : ∀  (a b c d e : Point) (AB BC AC CD DE AD : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d c e CD BC DE ∧ a.sameSide d BC ∧ b ≠ e ∧ |(b─c)| = |(c─e)| ∧
  distinctPointsOnLine a d AD ∧ (Triangle.area △ a:b:c = Triangle.area △ d:c:e) →
  ¬(AD.intersectsLine BC) := by
  euclid_intros

  have s1 : distinctPointsOnLine a d AD := by euclid_apply (h_1_40_s1 a d AD (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)))

  euclid_apply (proposition_31 a b c BC) as AF
  euclid_apply (intersection_lines AF CD) as f
  have s3 : a.onLine AF ∧ ¬(AF.intersectsLine BC) := by euclid_apply (h_1_40_s3 a AF BC (by (show a.onLine AF; assumption)) (by (show ¬AF.intersectsLine BC; assumption)))

  euclid_apply (line_from_points f e) as FE
  have s4 : distinctPointsOnLine f e FE := by euclid_apply (h_1_40_s4 a d f e FE AF BC (by (show f.onLine FE; assumption)) (by (show e.onLine FE; assumption)) (by (show f.onLine AF; assumption)) (by (show a.onLine AF; assumption)) (by (show e.onLine BC; assumption)) (by (show a.sameSide d BC; assumption)) (by (show ¬AF.intersectsLine BC; assumption)))

  have s5_a1 : |(b─c)| = |(c─e)| := by assumption

  have s5_a2 : ¬(AF.intersectsLine BC) := by assumption

  have s5 : Triangle.area △ a:b:c = Triangle.area △ f:c:e := by euclid_apply (h_1_40_s5 a b c f e AB BC AC CD AF FE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show f.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show e.onLine BC; assumption)) (by (show f.onLine FE; assumption)) (by (show e.onLine FE; assumption)) (by (show CD ≠ BC; assumption)) (by (show a.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show b ≠ e; assumption)) (by (show |(b─c)| = |(c─e)|; assumption)) (by (show ¬(AF.intersectsLine BC); assumption)))

  have s6 : Triangle.area △ a:b:c = Triangle.area △ d:c:e := by euclid_apply (h_1_40_s6 a b c d e (by (show Triangle.area △ a:b:c = Triangle.area △ d:c:e; assumption)))

  have s7 : Triangle.area △ d:c:e = Triangle.area △ f:c:e := by euclid_apply (h_1_40_s7 a b c d e f (by (show Triangle.area △ a:b:c = Triangle.area △ f:c:e; assumption)) (by (show Triangle.area △ a:b:c = Triangle.area △ d:c:e; assumption)))

  have s8 : False := by euclid_apply (h_1_40_s8 a b c d e f BC AF CD AD DE FE (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show e.onLine BC; assumption)) (by (show f.onLine FE; assumption)) (by (show e.onLine FE; assumption)) (by (show f.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show a.onLine AF; assumption)) (by (show f.onLine AF; assumption)) (by (show ¬AF.intersectsLine BC; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show a ≠ d; assumption)) (by (show AD.intersectsLine BC; assumption)) (by (show CD ≠ BC; assumption)) (by (show BC ≠ DE; assumption)) (by (show DE ≠ CD; assumption)) (by (show d ≠ c; assumption)) (by (show b ≠ e; assumption)) (by (show |(b─c)| = |(c─e)|; assumption)) (by (show a.sameSide d BC; assumption)) (by (show Triangle.area △ d:c:e = Triangle.area △ f:c:e; assumption)))

  exact s8

end Elements.Book1
