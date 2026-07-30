import SystemE
import Book1.Prop04.step1
import Book1.Prop04.step2
import Book1.Prop04.step3
import Book1.Prop04.step4
import Book1.Prop04.step5
import Book1.Prop04.step6
import Book1.Prop04.step7
import Book1.Prop04.step8
import Book1.Prop04.step9
import Book1.Prop04.step10
import Book1.Prop04.step11
import Book1.Prop04.step8_assumption1
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_4 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ (∠ b:a:c = ∠ e:d:f) →
  |(b─c)| = |(e─f)| ∧ (∠ a:b:c = ∠ d:e:f) ∧ (∠ a:c:b = ∠ d:f:e) := by
  euclid_intros

  euclid_apply (superposition a b c d e f AB BC AC DE) as (b', c', BC', DC')

  classical
  let ptImg : Point → Point := fun p =>
    if p = a then d else
    if p = b then b' else
    if p = c then c' else
    p

  let lineImg : Line → Line := fun L =>
    if L = AB then DE else
    if L = AC then DC' else
    if L = BC then BC' else
    L

  have h_ptImg_a : ptImg a = d := by simp (config := { zetaDelta := true })
  have h_ptImg_b : ptImg b = b' := by simp (config := { zetaDelta := true }) [Ne.symm right_3]
  have h_ptImg_c : ptImg c = c' := by
    have hca : c ≠ a := fun h => left_7 (two_points_determine_line b c AB BC
      ⟨⟨left_3, by rw [h]; assumption, fun heq => right_3 (heq.trans h).symm⟩, left_2, left_4⟩)
    have hcb : c ≠ b := fun h => right_8 (two_points_determine_line a c AB AC
      ⟨⟨by assumption, by rw [h]; assumption, fun heq => right_3 (heq.trans h)⟩, left_6, left_5⟩).symm
    simp (config := { zetaDelta := true }) [hca, hcb]
  have h_lineImg_AB : lineImg AB = DE := by simp (config := { zetaDelta := true })
  have h_lineImg_AC : lineImg AC = DC' := by simp (config := { zetaDelta := true }) [right_8]
  have h_lineImg_BC : lineImg BC = BC' := by
    simp (config := { zetaDelta := true }) [Ne.symm left_7, left_8]

  have s1_a1 : |(a─b)| = |(d─e)| := by assumption

  have s1 : ptImg b = e := by euclid_apply (h_1_4_s1 a b c d e b' c' DE (by (show a ≠ b; assumption)) (by (show |(a─b)| = |(d─b')|; assumption)) (by (show b'.onLine DE; assumption)) (by (show ¬between b' d e; assumption)) (by (show d.onLine DE; assumption)) (by (show e.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)))

  have s2_a1 : lineImg AB = DE := by simp (config := { zetaDelta := true })

  have s2_a2 : ∠ b:a:c = ∠ e:d:f := by assumption

  have s2 : lineImg AC = DF := by euclid_apply (h_1_4_s2 a b c d e f b' c' AB BC AC DE EF DF DC' BC' (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show lineImg AB = DE; assumption)) (by (show ∠ b:a:c = ∠ e:d:f; assumption)) (by (show ∠ b:a:c = ∠ b':d:c'; assumption)) (by (show c'.sameSide f DE; assumption)) (by (show d.onLine DC'; assumption)) (by (show c'.onLine DC'; assumption)) (by (show d ≠ c'; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show d.onLine DE; assumption)) (by (show b'.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show ptImg b = b'; assumption)) (by (show lineImg AC = DC'; assumption)) (by (show ptImg b = e; assumption)))

  have s3_a1 : |(a─c)| = |(d─f)| := by assumption

  have s3 : ptImg c = f := by euclid_apply (h_1_4_s3 a b c d e f b' c' AC DC' DE DF (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show |(a─c)| = |(d─f)|; assumption)) (by (show |(c─a)| = |(c'─d)|; assumption)) (by (show ∠ b:a:c = ∠ b':d:c'; assumption)) (by (show ∠ b:a:c = ∠ e:d:f; assumption)) (by (show c'.sameSide f DE; assumption)) (by (show d.onLine DE; assumption)) (by (show b'.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show d.onLine DC'; assumption)) (by (show c'.onLine DC'; assumption)) (by (show d ≠ c'; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show ptImg b = b'; assumption)) (by (show ptImg c = c'; assumption)) (by (show lineImg AC = DC'; assumption)) (by (show ptImg b = e; assumption)) (by (show lineImg AC = DF; assumption)))

  have s4_a1 : ptImg b = e := by assumption

  have s4 : lineImg BC = EF := by euclid_apply (h_1_4_s4 b c e f b' c' BC BC' EF (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show ptImg b = e; assumption)) (by (show b'.onLine BC'; assumption)) (by (show c'.onLine BC'; assumption)) (by (show b' ≠ c'; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show ptImg b = b'; assumption)) (by (show ptImg c = c'; assumption)) (by (show lineImg BC = BC'; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)))

  have habsurd : ¬ (lineImg BC ≠ EF) := by
    intro hne

    have s5_a1 : ptImg b = e := by assumption

    have s5_a2 : ptImg c = f := by assumption

    have s5_a3 : lineImg BC ≠ EF := by assumption

    have s5 : distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF := by euclid_apply (h_1_4_s5 b c e f b' c' BC BC' EF (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)) (by (show lineImg BC ≠ EF; assumption)) (by (show b'.onLine BC'; assumption)) (by (show c'.onLine BC'; assumption)) (by (show b' ≠ c'; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show ptImg b = b'; assumption)) (by (show ptImg c = c'; assumption)) (by (show lineImg BC = BC'; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)))

    have s6 : False := by euclid_apply (h_1_4_s6 e f BC BC' EF (by (show Line → Line; assumption)) (by (show lineImg BC ≠ EF; assumption)) (by (show lineImg BC = BC'; assumption)) (by (show distinctPointsOnLine e f (lineImg BC) ∧ distinctPointsOnLine e f EF; assumption)))
    exact s6

  have s7_a1 : lineImg BC = EF := by assumption

  have s7 : |(b─c)| = |(e─f)| := by euclid_apply (h_1_4_s7 b c e f b' c' BC EF (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show lineImg BC = EF; assumption)) (by (show |(b─c)| = |(b'─c')|; assumption)) (by (show ptImg b = b'; assumption)) (by (show ptImg c = c'; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)))

  have s8_a1 : ptImg a = d ∧ ptImg b = e ∧ ptImg c = f := by euclid_apply (h_1_4_s8_x1 a b c d e f b' c' (by (show Point → Point; assumption)) (by (show ptImg a = d; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)))

  have s8 : Triangle.area △ a:b:c = Triangle.area △ d:e:f := by euclid_apply (h_1_4_s8 a b c d e f b' c' (by (show Point → Point; assumption)) (by (show ptImg a = d ∧ ptImg b = e ∧ ptImg c = f; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(a─c)| = |(d─f)|; assumption)) (by (show ∠ b:a:c = ∠ b':d:c'; assumption)) (by (show ∠ a:c:b = ∠ d:c':b'; assumption)) (by (show ∠ c:b:a = ∠ c':b':d; assumption)) (by (show ptImg b = b'; assumption)) (by (show ptImg c = c'; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)))

  have s9 : ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e := by euclid_apply (h_1_4_s9 b c e f b' c' (by (show Point → Point; assumption)) (by (show ptImg a = d ∧ ptImg b = e ∧ ptImg c = f; assumption)) (by (show ∠ a:c:b = ∠ d:c':b'; assumption)) (by (show ∠ c:b:a = ∠ c':b':d; assumption)) (by (show ptImg b = b'; assumption)) (by (show ptImg c = c'; assumption)) (by (show ptImg b = e; assumption)) (by (show ptImg c = f; assumption)) (by (show |(b─c)| = |(b'─c')|; assumption)) (by (show b' ≠ c'; assumption)) (by (show a ≠ b; assumption)) (by (show d ≠ e; assumption)))

  have s10 : ∠ a:b:c = ∠ d:e:f := by euclid_apply (h_1_4_s10 (by (show ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e; assumption)))

  have s11 : ∠ a:c:b = ∠ d:f:e := by euclid_apply (h_1_4_s11 (by (show ∠ a:b:c = ∠ d:e:f ∧ ∠ a:c:b = ∠ d:f:e; assumption)))

  exact ⟨s7, s10, s11⟩

end Elements.Book1
