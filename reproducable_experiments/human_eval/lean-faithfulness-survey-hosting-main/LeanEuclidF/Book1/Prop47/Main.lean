import SystemE
import Book1.Prop04.Main
import Book1.Prop14.Main
import Book1.Prop31.Main
import Book1.Prop41.Main
import Book1Variants.Prop46
import Book1.Prop47.step1
import Book1.Prop47.step2
import Book1.Prop47.step3
import Book1.Prop47.step4
import Book1.Prop47.step5
import Book1.Prop47.step6
import Book1.Prop47.step7
import Book1.Prop47.step8
import Book1.Prop47.step9
import Book1.Prop47.step10
import Book1.Prop47.step11
import Book1.Prop47.step12
import Book1.Prop47.step13
import Book1.Prop47.step14
import Book1.Prop47.step15
import Book1.Prop47.step16
import Book1.Prop47.step17
import Book1.Prop47.step18
import Book1.Prop47.step19
import Book1.Prop47.step20
import Book1.Prop47.step21
import Book1.Prop47.hoffBD
import Book1.Prop47.hALDE
import Book1.Prop47.hALBC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_47 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros

  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  have s1 : (|(b─d)| = |(b─c)| ∧ |(c─e)| = |(b─c)| ∧ |(d─e)| = |(b─c)| ∧
        (∠ c:b:d = ∟) ∧ (∠ b:d:e = ∟) ∧ (∠ b:c:e = ∟) ∧ (∠ c:e:d = ∟)) ∧
      (|(a─g)| = |(a─b)| ∧ |(b─f)| = |(a─b)| ∧ |(g─f)| = |(a─b)| ∧
        (∠ b:a:g = ∟) ∧ (∠ a:g:f = ∟) ∧ (∠ a:b:f = ∟) ∧ (∠ b:f:g = ∟)) ∧
      (|(a─h)| = |(a─c)| ∧ |(c─k)| = |(a─c)| ∧ |(h─k)| = |(a─c)| ∧
        (∠ c:a:h = ∟) ∧ (∠ a:h:k = ∟) ∧ (∠ a:c:k = ∟) ∧ (∠ c:k:h = ∟)) := by euclid_apply (h_1_47_s1 b c d e BC DE BD CE a g f AB GF AG BF h k AC HK AH CK (by (show |(b─d)| = |(b─c)|; assumption)) (by (show |(c─e)| = |(b─c)|; assumption)) (by (show |(d─e)| = |(b─c)|; assumption)) (by (show (∠ c:b:d : ℝ) = ∟; assumption)) (by (show (∠ b:d:e : ℝ) = ∟; assumption)) (by (show (∠ b:c:e : ℝ) = ∟; assumption)) (by (show (∠ c:e:d : ℝ) = ∟; assumption)) (by (show |(a─g)| = |(a─b)|; assumption)) (by (show |(b─f)| = |(a─b)|; assumption)) (by (show |(g─f)| = |(a─b)|; assumption)) (by (show (∠ b:a:g : ℝ) = ∟; assumption)) (by (show (∠ a:g:f : ℝ) = ∟; assumption)) (by (show (∠ a:b:f : ℝ) = ∟; assumption)) (by (show (∠ b:f:g : ℝ) = ∟; assumption)) (by (show |(a─h)| = |(a─c)|; assumption)) (by (show |(c─k)| = |(a─c)|; assumption)) (by (show |(h─k)| = |(a─c)|; assumption)) (by (show (∠ c:a:h : ℝ) = ∟; assumption)) (by (show (∠ a:h:k : ℝ) = ∟; assumption)) (by (show (∠ a:c:k : ℝ) = ∟; assumption)) (by (show (∠ c:k:h : ℝ) = ∟; assumption)))

  have hoffBD : ¬(a.onLine BD) := by euclid_apply (h_1_47_x3 a b c AB BC AC d BD (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show (∠ c:b:d : ℝ) = ∟; assumption)) (by (show |(b─d)| = |(b─c)|; assumption)))
  euclid_apply (proposition_31 a b d BD) as AL
  have hALDE : AL.intersectsLine DE := by euclid_apply (h_1_47_x2 a b c d e AB BC AC AL BD DE (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a.onLine AL; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show |(b─d)| = |(b─c)|; assumption)) (by (show |(d─e)| = |(b─c)|; assumption)) (by (show (∠ b:d:e : ℝ) = ∟; assumption)))
  euclid_apply (intersection_lines AL DE) as l
  have s2 : a.onLine AL ∧ (¬(AL.intersectsLine BD) ∨ ¬(AL.intersectsLine CE)) := by euclid_apply (h_1_47_s2 a AL BD CE (by (show a.onLine AL; assumption)) (by (show ¬AL.intersectsLine BD; assumption)))

  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  have s3 : distinctPointsOnLine a d AD ∧ distinctPointsOnLine f c FC := by euclid_apply (h_1_47_s3 a b c d f AB BC AC BD BF AD FC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show f ≠ b; assumption)) (by (show (∠ a:b:f : ℝ) = ∟; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)))

  have s4_a1 : (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟) := by euclid_finish

  have s4 : c.opposingSides g AB ∧ (∠ b:a:c + ∠ b:a:g = ∟ + ∟) := by euclid_apply (h_1_47_s4 a b c g AB (by (show ¬g.sameSide c AB; assumption)) (by (show ¬g.onLine AB; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show (∠ b:a:c = ∟) ∧ (∠ b:a:g = ∟); assumption)))

  have s5 : between c a g := by euclid_apply (h_1_47_s5 a b c g AB AC AG (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AG; assumption)) (by (show g.onLine AG; assumption)) (by (show ¬g.sameSide c AB; assumption)) (by (show ¬g.onLine AB; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show (∠ b:a:g : ℝ) = ∟; assumption)))

  have s6 : between b a h := by euclid_apply (h_1_47_s6 a b c h AB AC AH (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show ¬h.sameSide b AC; assumption)) (by (show ¬h.onLine AC; assumption)) (by (show ¬b.onLine AC; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show (∠ c:a:h : ℝ) = ∟; assumption)))

  have s7_a1 : ∠ d:b:c = ∠ f:b:a := by euclid_finish

  have s7_a2 : (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟) := by euclid_finish

  have s7 : ∠ d:b:c + ∠ a:b:c = ∠ f:b:a + ∠ a:b:c := by euclid_apply (h_1_47_s7 a b c d f (by (show ∠ d:b:c = ∠ f:b:a; assumption)) (by (show (∠ d:b:c = ∟) ∧ (∠ f:b:a = ∟); assumption)))

  have s8 : ∠ d:b:a = ∠ f:b:c := by euclid_apply (h_1_47_s8 a b c d f g AB BC AC BD BF GF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show f ≠ b; assumption)) (by (show f.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show ¬c.onLine AB; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬d.sameSide a BC; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬g.onLine AB; assumption)) (by (show ¬g.sameSide c AB; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show (∠ c:b:d : ℝ) = ∟; assumption)) (by (show (∠ a:b:f : ℝ) = ∟; assumption)) (by (show ∠ d:b:c = ∠ f:b:a; assumption)))

  have s9_a1 : |(d─b)| = |(b─c)| := by euclid_finish

  have s9_a2 : |(f─b)| = |(b─a)| := by euclid_finish

  have s9 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)| := by euclid_apply (h_1_47_s9 a b c d f (by (show |(d─b)| = |(b─c)|; assumption)) (by (show |(f─b)| = |(b─a)|; assumption)))

  have s10 : ∠ d:b:a = ∠ f:b:c := by euclid_apply (h_1_47_s10 a b c d f (by (show ∠ d:b:a = ∠ f:b:c; assumption)))

  have s11 : |(a─d)| = |(f─c)| := by euclid_apply (h_1_47_s11 a b c d f AB BC AC BD AD FC BF (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show d.onLine AD; assumption)) (by (show a.onLine AD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show f ≠ b; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show (∠ a:b:f : ℝ) = ∟; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show |(d─b)| = |(b─c)|; assumption)) (by (show |(f─b)| = |(b─a)|; assumption)) (by (show ∠ d:b:a = ∠ f:b:c; assumption)))

  have s12 : Triangle.area △ a:b:d = Triangle.area △ f:b:c := by euclid_apply (h_1_47_s12 a b c d f AB BC AC BD AD FC BF (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show d.onLine AD; assumption)) (by (show a.onLine AD; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show f ≠ b; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show (∠ a:b:f : ℝ) = ∟; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show |(d─b)| = |(b─c)|; assumption)) (by (show |(f─b)| = |(b─a)|; assumption)) (by (show ∠ d:b:a = ∠ f:b:c; assumption)))

  have hALBC : AL.intersectsLine BC := by euclid_apply (h_1_47_x1 a b d AL BD BC (by (show a.onLine AL; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show b.onLine BC; assumption)) (by (show ¬d.onLine BC; assumption)))
  euclid_apply (intersection_lines AL BC) as m

  have s13_a1 : b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL) := by euclid_finish

  have s13 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:b:d + Triangle.area △ a:b:d := by euclid_apply (h_1_47_s13 a b d l m AB BC BD DE AL AD (by (show m.onLine AL; assumption)) (by (show l.onLine AL; assumption)) (by (show a.onLine AL; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show m.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show l.onLine DE; assumption)) (by (show d.onLine DE; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a.onLine AD; assumption)) (by (show d.onLine AD; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show b.onLine BD ∧ d.onLine BD ∧ ¬(BD.intersectsLine AL); assumption)))

  have s14_a1 : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC) := by euclid_finish

  have s14 : Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c := by euclid_apply (h_1_47_s14 a b c f g AB AC AG BF GF FC BC (by (show g.onLine AG; assumption)) (by (show a.onLine AG; assumption)) (by (show f.onLine BF; assumption)) (by (show b.onLine BF; assumption)) (by (show g.onLine GF; assumption)) (by (show f.onLine GF; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show c.onLine FC; assumption)) (by (show f.onLine FC; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show ¬g.onLine AB; assumption)) (by (show ¬AG.intersectsLine BF; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show between c a g; assumption)) (by (show f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC); assumption)))

  have s15 : Triangle.area △ a:b:d = Triangle.area △ f:b:c →
      Triangle.area △ a:b:d + Triangle.area △ a:b:d =
        Triangle.area △ f:b:c + Triangle.area △ f:b:c := by euclid_apply (h_1_47_s15 a b c d f)

  have s16 : Triangle.area △ b:m:l + Triangle.area △ b:l:d =
      Triangle.area △ a:g:f + Triangle.area △ a:f:b := by euclid_apply (h_1_47_s16 a b c d f g m l (by (show Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:b:d + Triangle.area △ a:b:d; assumption)) (by (show Triangle.area △ a:g:f + Triangle.area △ a:f:b = Triangle.area △ f:b:c + Triangle.area △ f:b:c; assumption)) (by (show Triangle.area △ a:b:d = Triangle.area △ f:b:c → Triangle.area △ a:b:d + Triangle.area △ a:b:d = Triangle.area △ f:b:c + Triangle.area △ f:b:c; assumption)) (by (show Triangle.area △ a:b:d = Triangle.area △ f:b:c; assumption)))

  euclid_apply (line_from_points a e) as AE
  euclid_apply (line_from_points b k) as BK
  have s17 : Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c := by euclid_apply (h_1_47_s17 a b c d e h k l m AB AC AL AE BK CE DE BC BD AH CK HK (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show a.onLine AL; assumption)) (by (show m.onLine AL; assumption)) (by (show l.onLine AL; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show m.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show b.onLine BC; assumption)) (by (show l.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d.onLine DE; assumption)) (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show c.onLine CK; assumption)) (by (show k.onLine CK; assumption)) (by (show h.onLine HK; assumption)) (by (show k.onLine HK; assumption)) (by (show b.onLine BK; assumption)) (by (show k.onLine BK; assumption)) (by (show b.onLine BD; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬b.onLine AC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show ¬h.onLine AC; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show ¬BD.intersectsLine CE; assumption)) (by (show ¬AH.intersectsLine CK; assumption)) (by (show ¬HK.intersectsLine AC; assumption)) (by (show between b a h; assumption)) (by (show |(c─e)| = |(b─c)|; assumption)) (by (show |(c─k)| = |(a─c)|; assumption)) (by (show (∠ b:c:e : ℝ) = ∟; assumption)) (by (show (∠ a:c:k : ℝ) = ∟; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show ¬d.sameSide a BC; assumption)) (by (show ¬h.sameSide b AC; assumption)))

  have s18 : Triangle.area △ b:d:e + Triangle.area △ b:e:c =
      (Triangle.area △ a:g:f + Triangle.area △ a:f:b) +
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c) := by euclid_apply (h_1_47_s18 a b c d e f g h k l m AB BC AC DE BD CE AL (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show a.onLine AL; assumption)) (by (show m.onLine AL; assumption)) (by (show m.onLine BC; assumption)) (by (show l.onLine AL; assumption)) (by (show l.onLine DE; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show ¬a.onLine BD; assumption)) (by (show ¬a.onLine BC; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show (∠ c:b:d : ℝ) = ∟; assumption)) (by (show (∠ b:c:e : ℝ) = ∟; assumption)) (by (show (∠ b:a:c : ℝ) = ∟; assumption)) (by (show ¬d.sameSide a BC; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬BD.intersectsLine CE; assumption)) (by (show ¬AL.intersectsLine BD; assumption)) (by (show Triangle.area △ b:m:l + Triangle.area △ b:l:d = Triangle.area △ a:g:f + Triangle.area △ a:f:b; assumption)) (by (show Triangle.area △ c:e:l + Triangle.area △ c:l:m = Triangle.area △ a:h:k + Triangle.area △ a:k:c; assumption)))

  have s19 : Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)| := by euclid_apply (h_1_47_s19 b c d e BC DE BD CE (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show b.onLine BD; assumption)) (by (show d.onLine BD; assumption)) (by (show c.onLine CE; assumption)) (by (show e.onLine CE; assumption)) (by (show ¬d.onLine BC; assumption)) (by (show (∠ c:b:d : ℝ) = ∟; assumption)) (by (show (∠ b:d:e : ℝ) = ∟; assumption)) (by (show |(b─d)| = |(b─c)|; assumption)) (by (show ¬DE.intersectsLine BC; assumption)) (by (show ¬BD.intersectsLine CE; assumption)))

  have s20 : (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|) := by euclid_apply (h_1_47_s20 a b c f g h k AB AC GF AG BF HK AH CK (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show g.onLine GF; assumption)) (by (show f.onLine GF; assumption)) (by (show a.onLine AG; assumption)) (by (show g.onLine AG; assumption)) (by (show b.onLine BF; assumption)) (by (show f.onLine BF; assumption)) (by (show f ≠ b; assumption)) (by (show g.sameSide a BF; assumption)) (by (show ¬GF.intersectsLine AB; assumption)) (by (show ¬AG.intersectsLine BF; assumption)) (by (show a.onLine AC; assumption)) (by (show c.onLine AC; assumption)) (by (show h.onLine HK; assumption)) (by (show k.onLine HK; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show c.onLine CK; assumption)) (by (show k.onLine CK; assumption)) (by (show k ≠ c; assumption)) (by (show h.sameSide a CK; assumption)) (by (show ¬HK.intersectsLine AC; assumption)) (by (show ¬AH.intersectsLine CK; assumption)) (by (show (∠ a:g:f : ℝ) = ∟; assumption)) (by (show (∠ a:h:k : ℝ) = ∟; assumption)) (by (show |(a─g)| = |(a─b)|; assumption)) (by (show |(a─h)| = |(a─c)|; assumption)))

  have s21 : |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by euclid_apply (h_1_47_s21 a b c d e f g h k (by (show Triangle.area △ b:d:e + Triangle.area △ b:e:c = (Triangle.area △ a:g:f + Triangle.area △ a:f:b) + (Triangle.area △ a:h:k + Triangle.area △ a:k:c); assumption)) (by (show Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)|; assumption)) (by (show (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧ (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|); assumption)))

  exact s21

end Elements.Book1
