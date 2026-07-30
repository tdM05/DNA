import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
import Mathlib.Tactic.Linarith
import Book1.Prop05.step1
import Book1.Prop05.step2
import Book1.Prop05.step3
import Book1.Prop05.step4
import Book1.Prop05.step5
import Book1.Prop05.step6
import Book1.Prop05.step7
import Book1.Prop05.step8
import Book1.Prop05.step9
import Book1.Prop05.step10
import Book1.Prop05.step11
import Book1.Prop05.step12
import Book1.Prop05.step13
import Book1.Prop05.step14
import Book1.Prop05.step15
import Book1.Prop05.step16
import Book1.Prop05.step17
import Book1.Prop05.step18
import Book1.Prop05.step19
import Book1.Prop05.step20
import Book1.Prop05.step21
import Book1.Prop05.step22
import Book1.Prop05.step23
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros

  euclid_apply (point_between_points_shorter_than AB b d (c─e)) as f
  have s1 : between b f d := by euclid_apply (h_1_5_s1 b f d (by (show between b f d; assumption)))

  euclid_apply (proposition_3 a e f a AC AB) as g
  have s2 : between a g e ∧ |(a─g)| = |(a─f)| := by euclid_apply (h_1_5_s2 a e f g (by (show between a g e; assumption)) (by (show |(a─g)| = |(f─a)|; assumption)))

  euclid_apply (line_from_points c f) as FC
  euclid_apply (line_from_points b g) as GB
  have s3 : c.onLine FC ∧ f.onLine FC ∧ b.onLine GB ∧ g.onLine GB := by euclid_apply (h_1_5_s3 c f b g FC GB (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)))

  have s4 : (|(f─a)| = |(g─a)|) ∧ (|(a─c)| = |(a─b)|) := by euclid_apply (h_1_5_s4 a b c f g (by (show |(a─g)| = |(a─f)|; assumption)) (by (show |(a─b)| = |(a─c)|; assumption)))

  have s5 : (∠ f:a:c = ∠ f:a:g) ∧ (∠ g:a:b = ∠ f:a:g) := by euclid_apply (h_1_5_s5 a b c d e f g AB AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)))

  have s6 : |(f─c)| = |(g─b)| := by euclid_apply (h_1_5_s6 a b c d e f g AB BC AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show f.onLine AB; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a g e; assumption)) (by (show between a c e; assumption)) (by (show |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|; assumption)) (by (show ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g; assumption)))

  have s7 : Triangle.area △ a:f:c = Triangle.area △ a:g:b := by euclid_apply (h_1_5_s7 a b c d e f g AB BC AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show f.onLine AB; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a g e; assumption)) (by (show between a c e; assumption)) (by (show |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|; assumption)) (by (show ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g; assumption)) (by (show |(f─c)| = |(g─b)|; assumption)))

  have s8 : (∠ a:c:f = ∠ a:b:g) ∧ (∠ a:f:c = ∠ a:g:b) := by euclid_apply (h_1_5_s8 a b c d e f g AB BC AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show f.onLine AB; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a g e; assumption)) (by (show between a c e; assumption)) (by (show |(f─a)| = |(g─a)| ∧ |(a─c)| = |(a─b)|; assumption)) (by (show ∠f:a:c = ∠f:a:g ∧ ∠g:a:b = ∠f:a:g; assumption)))

  have s9 : ∠ a:c:f = ∠ a:b:g := by euclid_apply (h_1_5_s9 a b c f g (by (show ∠a:c:f = ∠a:b:g ∧ ∠a:f:c = ∠a:g:b; assumption)))

  have s10 : ∠ a:f:c = ∠ a:g:b := by euclid_apply (h_1_5_s10 a b c f g (by (show ∠a:c:f = ∠a:b:g ∧ ∠a:f:c = ∠a:g:b; assumption)))

  have s11_a1 : |(a─f)| = |(a─g)| := by linarith

  have s11_a2 : |(a─b)| = |(a─c)| := by assumption

  have s11 : |(b─f)| = |(c─g)| := by euclid_apply (h_1_5_s11 a b c d e f g AB AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show |(a─f)| = |(a─g)|; assumption)) (by (show |(a─b)| = |(a─c)|; assumption)))

  have s12 : |(f─c)| = |(g─b)| := by euclid_apply (h_1_5_s12 f c g b (by (show |(f─c)| = |(g─b)|; assumption)))

  have s13 : (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|) := by euclid_apply (h_1_5_s13 b c f g (by (show |(b─f)| = |(c─g)|; assumption)) (by (show |(f─c)| = |(g─b)|; assumption)))

  have s14 : ∠ b:f:c = ∠ c:g:b := by euclid_apply (h_1_5_s14 a b c d e f g AB AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show AC ≠ AB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show |(a─f)| = |(a─g)|; assumption)) (by (show |(a─b)| = |(a─c)|; assumption)) (by (show ∠a:f:c = ∠a:g:b; assumption)))

  have s15 : distinctPointsOnLine b c BC := by euclid_apply (h_1_5_s15 a b c AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a ≠ b; assumption)) (by (show AC ≠ AB; assumption)))

  have s16 : Triangle.area △ b:f:c = Triangle.area △ c:g:b := by euclid_apply (h_1_5_s16 a b c d e f g AB BC AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|); assumption)) (by (show ∠b:f:c = ∠c:g:b; assumption)))

  have s17 : (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c) := by euclid_apply (h_1_5_s17 a b c d e f g AB BC AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show (|(b─f)| = |(c─g)|) ∧ (|(f─c)| = |(g─b)|); assumption)) (by (show ∠b:f:c = ∠c:g:b; assumption)))

  have s18 : ∠ f:b:c = ∠ g:c:b := by euclid_apply (h_1_5_s18 b c f g (by (show (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c); assumption)))

  have s19 : ∠ b:c:f = ∠ c:b:g := by euclid_apply (h_1_5_s19 a b c d e f g AB AC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show AC ≠ AB; assumption)) (by (show a ≠ b; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show distinctPointsOnLine b c BC; assumption)) (by (show (∠ f:b:c = ∠ g:c:b) ∧ (∠ f:c:b = ∠ g:b:c); assumption)))

  have s20_a1 : ∠ a:b:g = ∠ a:c:f := by linarith

  have s20_a2 : ∠ c:b:g = ∠ b:c:f := by linarith

  have s20 : ∠ a:b:c = ∠ a:c:b := by euclid_apply (h_1_5_s20 a b c d e f g AB BC AC FC GB (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine GB; assumption)) (by (show g.onLine GB; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show ∠ a:b:g = ∠ a:c:f; assumption)) (by (show ∠ c:b:g = ∠ b:c:f; assumption)) (by (show |(b─f)| = |(c─g)|; assumption)) (by (show |(a─f)| = |(a─g)|; assumption)) (by (show |(a─b)| = |(a─c)|; assumption)))

  have s21 : ∠ a:b:c = ∠ a:c:b := by euclid_apply (h_1_5_s21 a b c (by (show ∠ a:b:c = ∠ a:c:b; assumption)))

  have s22 : ∠ f:b:c = ∠ g:c:b := by euclid_apply (h_1_5_s22 b c f g (by (show ∠ f:b:c = ∠ g:c:b; assumption)))

  have s23 : (∠ f:b:c = ∠ c:b:d) ∧ (∠ g:c:b = ∠ b:c:e) := by euclid_apply (h_1_5_s23 a b c d e f g AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show f.onLine AB; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show distinctPointsOnLine b c BC; assumption)) (by (show between a b d; assumption)) (by (show between b f d; assumption)) (by (show between a c e; assumption)) (by (show between a g e; assumption)) (by (show |(b─f)| = |(c─g)|; assumption)) (by (show |(a─f)| = |(a─g)|; assumption)) (by (show |(a─b)| = |(a─c)|; assumption)))

  exact ⟨s21, s23.1.symm.trans (s22.trans s23.2)⟩

end Elements.Book1
