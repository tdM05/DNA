import SystemE
import Book1.Prop27.step1
import Book1.Prop27.step2
import Book1.Prop27.step3
import Book1.Prop27.step4
import Book1.Prop27.step5
import Book1.Prop27.step6
import Book1.Prop27.step7
import Book1.Prop27.step8
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_27 : ∀ (a d e f : Point) (AE FD EF : Line),
  distinctPointsOnLine a e AE ∧ distinctPointsOnLine f d FD ∧ distinctPointsOnLine e f EF ∧
  a.opposingSides d EF ∧ (∠ a:e:f = ∠ e:f:d) →
  ¬(AE.intersectsLine FD) := by

  euclid_intros

  euclid_apply (extend_point AE a e) as b
  euclid_apply (intersection_lines AE FD) as g

  have s1_a1 : AE.intersectsLine FD := by assumption

  have s1 : g.sameSide b EF ∨ g.opposingSides b EF := by euclid_apply (h_1_27_s1 a d e f b g AE FD EF (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show f.onLine FD; assumption)) (by (show d.onLine FD; assumption)) (by (show f ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show ¬a.onLine EF; assumption)) (by (show ¬d.onLine EF; assumption)) (by (show b.onLine AE; assumption)) (by (show between a e b; assumption)) (by (show g.onLine AE; assumption)) (by (show g.onLine FD; assumption)) (by (show AE.intersectsLine FD; assumption)))

  have hBD : ¬(g.sameSide b EF) := by
    intro hbd
    have s2 : g.onLine AE ∧ g.onLine FD ∧ g.sameSide b EF := by euclid_apply (h_1_27_s2 g b AE FD EF (by (show g.onLine AE; assumption)) (by (show g.onLine FD; assumption)) (by (show g.sameSide b EF; assumption)))
    have s3 : ∠ a:e:f = ∠ e:f:g := by euclid_apply (h_1_27_s3 a d e f g b AE FD EF (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a ≠ e; assumption)) (by (show f.onLine FD; assumption)) (by (show d.onLine FD; assumption)) (by (show f ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show ¬a.onLine EF; assumption)) (by (show ¬d.onLine EF; assumption)) (by (show ¬a.sameSide d EF; assumption)) (by (show ∠ a:e:f = ∠ e:f:d; assumption)) (by (show b.onLine AE; assumption)) (by (show between a e b; assumption)) (by (show g.onLine AE; assumption)) (by (show g.onLine FD; assumption)) (by (show g.sameSide b EF; assumption)))
    have s4 : False := by euclid_apply (h_1_27_s4 a d e f b g AE FD EF (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a ≠ e; assumption)) (by (show f.onLine FD; assumption)) (by (show d.onLine FD; assumption)) (by (show f ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show ∠ a:e:f = ∠ e:f:d; assumption)) (by (show ¬a.onLine EF; assumption)) (by (show ¬d.onLine EF; assumption)) (by (show ¬a.sameSide d EF; assumption)) (by (show AE.intersectsLine FD; assumption)) (by (show b.onLine AE; assumption)) (by (show between a e b; assumption)) (by (show g.onLine AE; assumption)) (by (show g.onLine FD; assumption)) (by (show g.sameSide b EF; assumption)) (by (show ∠ a:e:f = ∠ e:f:g; assumption)))
    exact s4
  have s5 : ¬(g.sameSide b EF) := by euclid_apply (h_1_27_s5 g b EF (by (show ¬g.sameSide b EF; assumption)))
  have s6 : ¬(g.opposingSides b EF) := by euclid_apply (h_1_27_s6 a d e f b g AE FD EF (by (show a.onLine AE; assumption)) (by (show e.onLine AE; assumption)) (by (show a ≠ e; assumption)) (by (show f.onLine FD; assumption)) (by (show d.onLine FD; assumption)) (by (show f ≠ d; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show e ≠ f; assumption)) (by (show ∠ a:e:f = ∠ e:f:d; assumption)) (by (show ¬a.onLine EF; assumption)) (by (show ¬d.onLine EF; assumption)) (by (show ¬a.sameSide d EF; assumption)) (by (show AE.intersectsLine FD; assumption)) (by (show b.onLine AE; assumption)) (by (show between a e b; assumption)) (by (show g.onLine AE; assumption)) (by (show g.onLine FD; assumption)))

  have s7_a1 : ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF) := by euclid_finish

  have s7 : ¬(AE.intersectsLine FD) := by euclid_apply (h_1_27_s7 g b AE FD EF (by (show g.sameSide b EF ∨ g.opposingSides b EF; assumption)) (by (show ¬(g.sameSide b EF) ∧ ¬(g.opposingSides b EF); assumption)))
  have s8 : ¬(AE.intersectsLine FD) := by euclid_apply (h_1_27_s8 AE FD (by (show ¬AE.intersectsLine FD; assumption)))

  exact s8 (by assumption)

end Elements.Book1
