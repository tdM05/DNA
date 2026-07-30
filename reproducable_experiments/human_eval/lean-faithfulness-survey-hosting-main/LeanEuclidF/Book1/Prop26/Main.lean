import SystemE
import Book1.Prop03.Main
import Book1.Prop04.Main
import Book1.Prop16.Main
import Mathlib.Tactic.Linarith
import Book1.Prop26.step1
import Book1.Prop26.step2
import Book1.Prop26.step3
import Book1.Prop26.step4
import Book1.Prop26.step5
import Book1.Prop26.step6
import Book1.Prop26.step7
import Book1.Prop26.step8
import Book1.Prop26.step9
import Book1.Prop26.step10
import Book1.Prop26.step11
import Book1.Prop26.step12
import Book1.Prop26.step13
import Book1.Prop26.step14
import Book1.Prop26.step15
import Book1.Prop26.step16
import Book1.Prop26.step17
import Book1.Prop26.step18
import Book1.Prop26.step19
import Book1.Prop26.step24
import Book1.Prop26.step25
import Book1.Prop26.step26
import Book1.Prop26.step27
import Book1.Prop26.step28
import Book1.Prop26.step29
import Book1.Prop26.step30
import Book1.Prop26.step31
import Book1.Prop26.step32
import Book1.Prop26.step33
import Book1.Prop26.step34
import Book1.Prop26.step35
import Book1.Prop26.step36
import Book1.Prop26.step37
import Book1.Prop26.step38
import Book1.Prop26.step39
import Book1.Prop26.step40
import Book1.Prop26.step41
import Book1.Prop26.step42
import Book1.Prop26.h_sym
import Book1.Prop26.h_sym2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_26 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  (∠ a:b:c = ∠ d:e:f) ∧ (∠ b:c:a = ∠ e:f:d) ∧ (|(b─c)| = |(e─f)| ∨ |(a─b)| = |(d─e)|) →
  (|(a─b)| = |(d─e)|) ∧ (|(b─c)| = |(e─f)|) ∧ (|(a─c)| = |(d─f)|) ∧ (∠ b:a:c = ∠ e:d:f) := by
  euclid_intros

  split_ors

  ·
    have habsurd1 : ¬(|(a─b)| ≠ |(d─e)|) := by
      intro hne
      have s1 : |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)| := by euclid_apply (h_1_26_s1 a b d e (by (show |(a─b)| ≠ |(d─e)|; assumption)))
      wlog hgt : |(a─b)| > |(d─e)| generalizing a b c d e f AB BC AC DE EF DF with Hsym

      ·
        have h_sym : False := by euclid_apply (h_1_26_x1 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)) (by (show ∠ b:c:a = ∠ e:f:d; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show |(a─b)| > |(d─e)| ∨ |(d─e)| > |(a─b)|; assumption)) (by (show ¬|(a─b)| > |(d─e)|; assumption)))
        exact h_sym
      · euclid_apply (proposition_3 b a e d AB DE) as g
        euclid_apply (line_from_points g c) as GC
        have s2 : between b g a ∧ |(b─g)| = |(d─e)| ∧ g.onLine GC ∧ c.onLine GC := by euclid_apply (h_1_26_s2 b g a d e c GC (by (show between b g a; assumption)) (by (show |(b─g)| = |(e─d)|; assumption)) (by (show g.onLine GC; assumption)) (by (show c.onLine GC; assumption)))

        have s3_a1 : |(b─g)| = |(d─e)| := by linarith

        have s3_a2 : |(b─c)| = |(e─f)| := by assumption

        have s3 : |(g─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| := by euclid_apply (h_1_26_s3 b g d e c (by (show |(b─g)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)))
        have s4 : ∠ g:b:c = ∠ d:e:f := by euclid_apply (h_1_26_s4 a b c d e f g AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b g a; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
        have s5 : |(g─c)| = |(d─f)| := by euclid_apply (h_1_26_s5 a b c d e f g AB BC DE EF DF GC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show g.onLine GC; assumption)) (by (show c.onLine GC; assumption)) (by (show between b g a; assumption)) (by (show |(b─g)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ g:b:c = ∠ d:e:f; assumption)))
        have s6 : Triangle.area △ g:b:c = Triangle.area △ d:e:f := by euclid_apply (h_1_26_s6 a b c d e f g AB BC DE EF DF GC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show g.onLine GC; assumption)) (by (show c.onLine GC; assumption)) (by (show between b g a; assumption)) (by (show |(b─g)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show |(g─c)| = |(d─f)|; assumption)) (by (show ∠ g:b:c = ∠ d:e:f; assumption)))
        have s7 : ∠ b:g:c = ∠ e:d:f ∧ ∠ g:c:b = ∠ d:f:e := by euclid_apply (h_1_26_s7 a b c d e f g AB BC DE EF DF GC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show g.onLine GC; assumption)) (by (show c.onLine GC; assumption)) (by (show between b g a; assumption)) (by (show |(b─g)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ g:b:c = ∠ d:e:f; assumption)))
        have s8 : ∠ g:c:b = ∠ d:f:e := by euclid_apply (h_1_26_s8 (by (show ∠ b:g:c = ∠ e:d:f ∧ ∠ g:c:b = ∠ d:f:e; assumption)))
        have s9 : ∠ d:f:e = ∠ b:c:a := by euclid_apply (h_1_26_s9 (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show e.onLine DE; assumption)) (by (show d.onLine DE; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show d ≠ e; assumption)) (by (show ∠ b:c:a = ∠ e:f:d; assumption)))
        have s10 : ∠ b:c:g = ∠ b:c:a := by euclid_apply (h_1_26_s10 a b c g AB BC AC GC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show g.onLine GC; assumption)) (by (show c.onLine GC; assumption)) (by (show between b g a; assumption)) (by (show ∠ g:c:b = ∠ d:f:e; assumption)) (by (show ∠ d:f:e = ∠ b:c:a; assumption)))
        have s11 : False := by euclid_apply (h_1_26_s11 a b c g AB BC AC GC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show g.onLine GC; assumption)) (by (show c.onLine GC; assumption)) (by (show between b g a; assumption)) (by (show ∠ b:c:g = ∠ b:c:a; assumption)))
        exact s11

    have s12 : ¬(|(a─b)| ≠ |(d─e)|) := by euclid_apply (h_1_26_s12 (by (show ¬|(a─b)| ≠ |(d─e)|; assumption)))
    have s13 : |(a─b)| = |(d─e)| := by euclid_apply (h_1_26_s13 (by (show ¬|(a─b)| ≠ |(d─e)|; assumption)))
    have s14 : |(b─c)| = |(e─f)| := by euclid_apply (h_1_26_s14 (by (show |(b─c)| = |(e─f)|; assumption)))
    have s15 : |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| := by euclid_apply (h_1_26_s15 (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)))
    have s16 : ∠ a:b:c = ∠ d:e:f := by euclid_apply (h_1_26_s16 (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    have s17 : |(a─c)| = |(d─f)| := by euclid_apply (h_1_26_s17 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    have s18 : ∠ b:a:c = ∠ e:d:f := by euclid_apply (h_1_26_s18 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    exact ⟨s13, s14, s17, s18⟩

  ·
    have s19 : |(a─b)| = |(d─e)| := by euclid_apply (h_1_26_s19 (by (show |(a─b)| = |(d─e)|; assumption)))

    have habsurd2 : ¬(|(b─c)| ≠ |(e─f)|) := by
      intro hne2
      have s24 : |(b─c)| > |(e─f)| ∨ |(e─f)| > |(b─c)| := by euclid_apply (h_1_26_s24 (by (show |(b─c)| ≠ |(e─f)|; assumption)))
      wlog hgt2 : |(b─c)| > |(e─f)| generalizing a b c d e f AB BC AC DE EF DF with Hsym2

      ·
        have h_sym2 : False := by euclid_apply (h_1_26_x2 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DF; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)) (by (show ∠ b:c:a = ∠ e:f:d; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| > |(e─f)| ∨ |(e─f)| > |(b─c)|; assumption)) (by (show ¬|(b─c)| > |(e─f)|; assumption)))
        exact h_sym2
      · euclid_apply (proposition_3 b c e f BC EF) as h
        euclid_apply (line_from_points a h) as AH
        have s25 : between b h c ∧ |(b─h)| = |(e─f)| ∧ a.onLine AH ∧ h.onLine AH := by euclid_apply (h_1_26_s25 a b c e f h AH (by (show between b h c; assumption)) (by (show |(b─h)| = |(e─f)|; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)))

        have s26_a1 : |(b─h)| = |(e─f)| := by assumption

        have s26_a2 : |(a─b)| = |(d─e)| := by assumption

        have s26 : |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)| := by euclid_apply (h_1_26_s26 h (by (show |(b─h)| = |(e─f)|; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)))
        have s27 : ∠ a:b:h = ∠ d:e:f := by euclid_apply (h_1_26_s27 a b c d e f h AB BC AC (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show between b h c; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
        have s28 : |(a─h)| = |(d─f)| := by euclid_apply (h_1_26_s28 a b c d e f h AB BC AH DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show between b h c; assumption)) (by (show |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)|; assumption)) (by (show ∠ a:b:h = ∠ d:e:f; assumption)))
        have s29 : Triangle.area △ a:b:h = Triangle.area △ d:e:f := by euclid_apply (h_1_26_s29 a b c d e f h AB BC AH DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show between b h c; assumption)) (by (show |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)|; assumption)) (by (show ∠ a:b:h = ∠ d:e:f; assumption)) (by (show |(a─h)| = |(d─f)|; assumption)))
        have s30 : ∠ b:a:h = ∠ e:d:f ∧ ∠ b:h:a = ∠ e:f:d := by euclid_apply (h_1_26_s30 a b c d e f h AB BC AH DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show between b h c; assumption)) (by (show |(a─b)| = |(d─e)| ∧ |(b─h)| = |(e─f)|; assumption)) (by (show ∠ a:b:h = ∠ d:e:f; assumption)))
        have s31 : ∠ b:h:a = ∠ e:f:d := by euclid_apply (h_1_26_s31 (by (show ∠ b:a:h = ∠ e:d:f ∧ ∠ b:h:a = ∠ e:f:d; assumption)))
        have s32 : ∠ e:f:d = ∠ b:c:a := by euclid_apply (h_1_26_s32 (by (show ∠ b:c:a = ∠ e:f:d; assumption)))
        have s33 : ∠ b:h:a = ∠ b:c:a := by euclid_apply (h_1_26_s33 (by (show ∠ b:h:a = ∠ e:f:d; assumption)) (by (show ∠ e:f:d = ∠ b:c:a; assumption)))
        have s34 : False := by euclid_apply (h_1_26_s34 a b c h AB BC AC AH (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show AB ≠ BC; assumption)) (by (show BC ≠ AC; assumption)) (by (show AC ≠ AB; assumption)) (by (show a.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show between b h c; assumption)) (by (show ∠ b:h:a = ∠ b:c:a; assumption)))
        exact s34

    have s35 : ¬(|(b─c)| ≠ |(e─f)|) := by euclid_apply (h_1_26_s35 (by (show ¬(|(b─c)| ≠ |(e─f)|); assumption)))
    have s36 : |(b─c)| = |(e─f)| := by euclid_apply (h_1_26_s36 (by (show ¬(|(b─c)| ≠ |(e─f)|); assumption)))
    have s37 : |(a─b)| = |(d─e)| := by euclid_apply (h_1_26_s37 (by (show |(a─b)| = |(d─e)|; assumption)))
    have s38 : |(a─b)| = |(d─e)| ∧ |(b─c)| = |(e─f)| := by euclid_apply (h_1_26_s38 (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)))
    have s39 : ∠ a:b:c = ∠ d:e:f := by euclid_apply (h_1_26_s39 (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    have s40 : |(a─c)| = |(d─f)| := by euclid_apply (h_1_26_s40 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    have s41 : Triangle.area △ a:b:c = Triangle.area △ d:e:f := by euclid_apply (h_1_26_s41 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    have s42 : ∠ b:a:c = ∠ e:d:f := by euclid_apply (h_1_26_s42 a b c d e f AB BC AC DE EF DF (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show b.onLine BC; assumption)) (by (show c.onLine BC; assumption)) (by (show c.onLine AC; assumption)) (by (show a.onLine AC; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show AB ≠ BC; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)) (by (show ∠ a:b:c = ∠ d:e:f; assumption)))
    exact ⟨s37, s36, s40, s42⟩

end Elements.Book1
