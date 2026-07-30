import SystemE
import Book1.Prop08.step1
import Book1.Prop08.step2
import Book1.Prop08.step3
import Book1.Prop08.step4
import Book1.Prop08.step5
import Book1.Prop08.step6
import Book1.Prop08.step7
import Book1.Prop08.step8
import Book1.Prop08.step9
import Book1.Prop08.step10
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_8 : ∀ (a b c d e f : Point) (AB BC AC DE EF DF : Line),
  formTriangle a b c AB BC AC ∧ formTriangle d e f DE EF DF ∧
  |(a─b)| = |(d─e)| ∧ |(a─c)| = |(d─f)| ∧ |(b─c)| = |(e─f)| →
  ∠ b:a:c = ∠ e:d:f := by
  euclid_intros

  euclid_apply (superposition b c a e f d BC AC AB EF) as (c', g, GF, EG)

  classical
  let ptImg : Point → Point := fun p =>
    if p = b then e else
    if p = c then c' else
    if p = a then g else
    p
  let lineImg : Line → Line := fun L =>
    if L = BC then EF else
    if L = AB then EG else
    if L = AC then GF else
    L

  have h_ptImg_c : ptImg c = c' := by
    have hcb : c ≠ b := by clear ptImg lineImg; euclid_finish
    simp (config := { zetaDelta := true }) [hcb]
  have h_lineImg_AB : lineImg AB = EG := by
    simp (config := { zetaDelta := true }) [left_7]
  have h_lineImg_AC : lineImg AC = GF := by
    simp (config := { zetaDelta := true }) [Ne.symm left_8, right_8]

  have s1_a1 : |(b─c)| = |(e─f)| := by assumption

  have s1 : ptImg c = f := by euclid_apply (h_1_8_s1 b c c' e f EF (by (show Point → Point; assumption)) (by (show ptImg c = c'; assumption)) (by (show c'.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show |(b─c)| = |(e─c')|; assumption)) (by (show ¬between c' e f; assumption)) (by (show |(b─c)| = |(e─f)|; assumption)))

  have s2_a1 : lineImg BC = EF := by simp (config := { zetaDelta := true })

  have s2 : lineImg AB = DE ∧ lineImg AC = DF := by euclid_apply (h_1_8_s2 a b c d e f c' g AB BC AC DE EF DF EG GF (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show ptImg c = c'; assumption)) (by (show lineImg AB = EG; assumption)) (by (show lineImg AC = GF; assumption)) (by (show lineImg BC = EF; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine GF; assumption)) (by (show c'.onLine GF; assumption)) (by (show c'.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.sameSide d EF; assumption)) (by (show e.onLine DE; assumption)) (by (show d.onLine DE; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show e ≠ g; assumption)) (by (show d ≠ e; assumption)) (by (show c' ≠ g; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(a─b)| = |(g─e)|; assumption)) (by (show |(c─a)| = |(c'─g)|; assumption)) (by (show |(a─c)| = |(d─f)|; assumption)) (by (show ptImg c = f; assumption)))

  have habsurd : ¬ (lineImg AB ≠ DE ∧ lineImg AC ≠ DF) := by
    intro hne

    have s3_a1 : lineImg BC = EF := by assumption

    have s3 : lineImg AB ≠ DE ∧ lineImg AC ≠ DF := by euclid_apply (h_1_8_s3 AB BC AC DE EF DF (by (show Line → Line; assumption)) (by (show lineImg BC = EF; assumption)) (by (show lineImg AB ≠ DE ∧ lineImg AC ≠ DF; assumption)))
    have s4 : distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧ distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)| := by euclid_apply (h_1_8_s4 a b c d e f c' g EF EG GF DE DF (by (show Point → Point; assumption)) (by (show ptImg c = c'; assumption)) (by (show c'.onLine GF; assumption)) (by (show g.onLine GF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e.onLine EG; assumption)) (by (show g.onLine EG; assumption)) (by (show e.onLine DE; assumption)) (by (show d.onLine DE; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show e ≠ g; assumption)) (by (show c' ≠ g; assumption)) (by (show d ≠ e; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show |(a─b)| = |(d─e)|; assumption)) (by (show |(a─b)| = |(g─e)|; assumption)) (by (show |(c─a)| = |(c'─g)|; assumption)) (by (show |(a─c)| = |(d─f)|; assumption)) (by (show ptImg c = f; assumption)))
    have s5 : g ≠ d ∧ g.sameSide d EF := by euclid_apply (h_1_8_s5 d e f g AB AC DE EF DF EG GF (by (show Line → Line; assumption)) (by (show lineImg AB = EG; assumption)) (by (show lineImg AB ≠ DE ∧ lineImg AC ≠ DF; assumption)) (by (show distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧ distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)|; assumption)) (by (show e.onLine DE; assumption)) (by (show d.onLine DE; assumption)) (by (show d ≠ e; assumption)) (by (show g.sameSide d EF; assumption)))
    have s6 : (e.onLine EG ∧ e.onLine DE) ∧ (f.onLine GF ∧ f.onLine DF) := by euclid_apply (h_1_8_s6 c' e f DE EF DF EG GF (by (show Point → Point; assumption)) (by (show ptImg c = c'; assumption)) (by (show e.onLine EG; assumption)) (by (show e.onLine DE; assumption)) (by (show c'.onLine GF; assumption)) (by (show f.onLine DF; assumption)) (by (show ptImg c = f; assumption)))
    have s7 : False := by euclid_apply (h_1_8_s7 d e f g DE EF DF EG GF (by (show d.onLine DE; assumption)) (by (show d.onLine DF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show d ≠ e; assumption)) (by (show DE ≠ EF; assumption)) (by (show EF ≠ DF; assumption)) (by (show DF ≠ DE; assumption)) (by (show distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG ∧ distinctPointsOnLine g f GF ∧ |(e─g)| = |(e─d)| ∧ |(g─f)| = |(f─d)|; assumption)) (by (show g ≠ d ∧ g.sameSide d EF; assumption)) (by (show (e.onLine EG ∧ e.onLine DE) ∧ f.onLine GF ∧ f.onLine DF; assumption)))
    exact s7

  have s8 : ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF) := by euclid_apply (h_1_8_s8 AB AC DE DF (by (show Line → Line; assumption)) (by (show lineImg AB = DE ∧ lineImg AC = DF; assumption)))

  have s9 : lineImg AB = DE ∧ lineImg AC = DF := by euclid_apply (h_1_8_s9 AB AC DE DF (by (show Line → Line; assumption)) (by (show ¬ (lineImg AB ≠ DE) ∧ ¬ (lineImg AC ≠ DF); assumption)))

  have s10 : ∠ b:a:c = ∠ e:d:f := by euclid_apply (h_1_8_s10 a b c c' d e f g AB AC BC DE EF DF EG GF (by (show Point → Point; assumption)) (by (show Line → Line; assumption)) (by (show ptImg c = c'; assumption)) (by (show lineImg AB = EG; assumption)) (by (show lineImg AC = GF; assumption)) (by (show ∠ b:a:c = ∠ e:g:c'; assumption)) (by (show g.onLine EG; assumption)) (by (show g.onLine GF; assumption)) (by (show d.onLine DE; assumption)) (by (show d.onLine DF; assumption)) (by (show c'.onLine EF; assumption)) (by (show c'.onLine GF; assumption)) (by (show f.onLine EF; assumption)) (by (show f.onLine DF; assumption)) (by (show e ≠ g; assumption)) (by (show d ≠ e; assumption)) (by (show DF ≠ DE; assumption)) (by (show EF ≠ DF; assumption)) (by (show ptImg c = f; assumption)) (by (show lineImg AB = DE ∧ lineImg AC = DF; assumption)))

  exact s10

end Elements.Book1
