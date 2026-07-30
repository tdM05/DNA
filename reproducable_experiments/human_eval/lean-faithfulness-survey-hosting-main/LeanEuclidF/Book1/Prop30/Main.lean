import SystemE
import Book1.Prop30.step1
import Book1.Prop30.step2
import Book1.Prop30.step3
import Book1.Prop30.step4
import Book1.Prop30.step5
import Book1.Prop30.step6
import Book1.Prop30.step7
import Book1.Prop30.step7_othercases
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_30 : ∀ (AB CD EF : Line),
  AB ≠ CD ∧ CD ≠ EF ∧ EF ≠ AB ∧ ¬(AB.intersectsLine EF) ∧ ¬(CD.intersectsLine EF) →
  ¬(AB.intersectsLine CD) := by
  euclid_intros

  euclid_apply (line_nonempty AB) as g
  euclid_apply (exists_distincts_points_on_line CD g) as k
  euclid_apply (line_from_points g k) as GK
  euclid_apply (intersection_lines EF GK) as h
  euclid_apply (exists_distincts_points_on_line AB g) as a
  euclid_apply (extend_point AB a g) as b
  euclid_apply (point_on_line_same_side GK EF a) as e
  euclid_apply (extend_point EF e h) as f
  euclid_apply (point_on_line_same_side GK CD a) as c
  euclid_apply (extend_point CD c k) as d

  have s1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ CD.intersectsLine GK := by euclid_apply (h_1_30_s1 AB CD EF GK g h k (by (show g.onLine AB; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine EF; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine CD; assumption)) (by (show k.onLine GK; assumption)) (by (show EF ≠ AB; assumption)) (by (show CD ≠ EF; assumption)) (by (show ¬AB.intersectsLine EF; assumption)) (by (show ¬CD.intersectsLine EF; assumption)))

  by_cases hc : between g h k
  ·

    have s2_a1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF) := by euclid_finish

    have s2 : ∠ a:g:k = ∠ g:h:f := by euclid_apply (h_1_30_s2 AB EF GK a b e f g h k (by (show g.onLine AB; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine EF; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show between a g b; assumption)) (by (show between e h f; assumption)) (by (show between g h k; assumption)) (by (show e.sameSide a GK; assumption)) (by (show ¬AB.intersectsLine EF; assumption)) (by (show AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF); assumption)))

    have s3_a1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF) := by euclid_finish

    have s3 : ∠ g:h:f = ∠ g:k:d := by euclid_apply (h_1_30_s3 EF CD GK c d e f g h k (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show h.onLine EF; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show k.onLine CD; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between e h f; assumption)) (by (show between c k d; assumption)) (by (show between g h k; assumption)) (by (show e.sameSide a GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show ¬CD.intersectsLine EF; assumption)) (by (show EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF); assumption)))

    have s4 : ∠ a:g:k = ∠ g:h:f := by euclid_apply (h_1_30_s4 (by (show ∠ a:g:k = ∠ g:h:f; assumption)))

    have s5 : ∠ a:g:k = ∠ g:k:d := by euclid_apply (h_1_30_s5 (by (show ∠ a:g:k = ∠ g:h:f; assumption)) (by (show ∠ g:h:f = ∠ g:k:d; assumption)))

    have s6 : a.opposingSides d GK := by euclid_apply (h_1_30_s6 GK a c d k (by (show k.onLine GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show between c k d; assumption)))

    have s7 : ¬(AB.intersectsLine CD) := by euclid_apply (h_1_30_s7 AB CD GK a d g k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show k.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show g.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show g ≠ a; assumption)) (by (show between c k d; assumption)) (by (show between g h k; assumption)) (by (show ∠ a:g:k = ∠ g:k:d; assumption)) (by (show a.opposingSides d GK; assumption)))

    exact s7 (by assumption)
  ·
    have s7_x4 : ¬(AB.intersectsLine CD) := by euclid_apply (h_1_30_s7_x1 AB CD EF GK a b c d e f g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show k.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between e h f; assumption)) (by (show between c k d; assumption)) (by (show e.sameSide a GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show ¬AB.intersectsLine EF; assumption)) (by (show ¬CD.intersectsLine EF; assumption)) (by (show ¬between g h k; assumption)) (by (show g ≠ k; assumption)) (by (show CD ≠ EF; assumption)) (by (show EF ≠ AB; assumption)))
    exact s7_x4 (by assumption)

end Elements.Book1
