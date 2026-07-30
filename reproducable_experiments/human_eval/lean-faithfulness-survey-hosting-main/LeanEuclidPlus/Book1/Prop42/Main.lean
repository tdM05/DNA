import SystemE
import Book1.Prop10.Main
import Book1Variants.Prop23
import Book1.Prop31.Main
import Book1.Prop38.Main
import Book1.Prop41.Main
import Book1.Prop42.step1
import Book1.Prop42.step2
import Book1.Prop42.step3
import Book1.Prop42.step4
import Book1.Prop42.step5
import Book1.Prop42.step6
import Book1.Prop42.step7
import Book1.Prop42.step8
import Book1.Prop42.step9
import Book1.Prop42.step10
import Book1.Prop42.step11
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_42 : ∀ (a b c d₁ d₂ d₃ : Point) (AB BC AC D₁₂ D₂₃: Line),
  formTriangle a b c AB BC AC ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (f g e c' : Point) (FG EC EF CG : Line), formParallelogram f g e c' FG EC EF CG ∧
  (∠ c':e:f = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ f:e:c' + Triangle.area △ f:c':g = Triangle.area △ a:b:c) := by
  euclid_intros

  euclid_apply (proposition_10 b c BC) as e
  have s1 : between b e c ∧ |(b─e)| = |(e─c)| := by euclid_apply (h_1_42_s1 b e c (by (show between b e c; assumption)) (by (show |(b─e)| = |(e─c)|; assumption)))

  euclid_apply (line_from_points a e) as AE
  have s2 : distinctPointsOnLine a e AE := by euclid_apply (h_1_42_s2 a b c e AB BC AE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show between b e c; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)))

  euclid_apply (proposition_23' e c d₂ d₁ d₃ a BC D₁₂ D₂₃) as f₀
  euclid_apply (line_from_points e f₀) as EF
  have s3 : ∠ c:e:f₀ = ∠ d₁:d₂:d₃ := by euclid_apply (h_1_42_s3 b c e f₀ d₁ d₂ d₃ (by (show f₀ ≠ e; assumption)) (by (show between b e c; assumption)) (by (show ∠f₀:e:c = ∠d₁:d₂:d₃; assumption)))

  euclid_apply (proposition_31 a b c BC) as AG
  euclid_apply (intersection_lines AG EF) as f
  have s4 : a.onLine AG ∧ ¬(AG.intersectsLine BC) := by euclid_apply (h_1_42_s4 a AG BC (by (show a.onLine AG; assumption)) (by (show ¬AG.intersectsLine BC; assumption)))

  euclid_apply (proposition_31 c e f EF) as CG
  euclid_apply (intersection_lines CG AG) as g
  have s5 : c.onLine CG ∧ ¬(CG.intersectsLine EF) := by euclid_apply (h_1_42_s5 c CG EF (by (show c.onLine CG; assumption)) (by (show ¬CG.intersectsLine EF; assumption)))

  have s6 : formParallelogram f g e c AG BC EF CG := by euclid_apply (h_1_42_s6 a b e f g c AB BC AG EF CG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show a.onLine AG; assumption)) (by (show f.onLine AG; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine CG; assumption)) (by (show g.onLine AG; assumption)) (by (show e.onLine EF; assumption)) (by (show c.onLine CG; assumption)) (by (show between b e c; assumption)) (by (show ¬AG.intersectsLine BC; assumption)) (by (show ¬CG.intersectsLine EF; assumption)))

  have s7_a1 : |(b─e)| = |(e─c)| := by assumption

  have s7_a2 : |(b─e)| = |(e─c)| := by assumption

  have s7_a3 : ¬(AG.intersectsLine BC) := by assumption

  have s7 : Triangle.area △ a:b:e = Triangle.area △ a:e:c := by euclid_apply (h_1_42_s7 a b c e AB BC AC AE AG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a.onLine AG; assumption)) (by (show ¬(AG.intersectsLine BC); assumption)) (by (show between b e c; assumption)) (by (show |(b─e)| = |(e─c)|; assumption)) (by (show |(b─e)| = |(e─c)|; assumption)) (by (show ¬(AG.intersectsLine BC); assumption)))

  have s8 : Triangle.area △ a:b:c = Triangle.area △ a:e:c + Triangle.area △ a:e:c := by euclid_apply (h_1_42_s8 a b c e AB BC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show between b e c; assumption)) (by (show Triangle.area △ a:b:e = Triangle.area △ a:e:c; assumption)))

  have s9_a1 : distinctPointsOnLine e c BC := by euclid_finish

  have s9_a2 : ¬(AG.intersectsLine BC) := by assumption

  have s9 : Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:e:c + Triangle.area △ a:e:c := by euclid_apply (h_1_42_s9 a b c e f g AB BC AC AE AG EF CG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show AB ≠ BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a.onLine AG; assumption)) (by (show between b e c; assumption)) (by (show formParallelogram f g e c AG BC EF CG; assumption)) (by (show distinctPointsOnLine e c BC; assumption)) (by (show ¬(AG.intersectsLine BC); assumption)))

  have s10 : Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:b:c := by euclid_apply (h_1_42_s10 a b c e f g (by (show Triangle.area △ a:b:c = Triangle.area △ a:e:c + Triangle.area △ a:e:c; assumption)) (by (show Triangle.area △ f:e:c + Triangle.area △ f:c:g = Triangle.area △ a:e:c + Triangle.area △ a:e:c; assumption)))

  have s11 : ∠ c:e:f = ∠ d₁:d₂:d₃ := by euclid_apply (h_1_42_s11 a b c e f f₀ d₁ d₂ d₃ BC EF AG (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f₀.onLine EF; assumption)) (by (show f₀ ≠ e; assumption)) (by (show f₀.onLine BC ∨ f₀.sameSide a BC; assumption)) (by (show f.onLine AG; assumption)) (by (show a.onLine AG; assumption)) (by (show ¬AG.intersectsLine BC; assumption)) (by (show between b e c; assumption)) (by (show ∠ d₁:d₂:d₃ > 0; assumption)) (by (show ∠ d₁:d₂:d₃ < ∟ + ∟; assumption)) (by (show ∠ c:e:f₀ = ∠ d₁:d₂:d₃; assumption)))

  use f, g, e, c, AG, BC, EF, CG

end Elements.Book1
