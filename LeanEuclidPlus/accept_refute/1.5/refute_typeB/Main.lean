import SystemE
import Mathlib.Tactic.Linarith


set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1


theorem proposition_5_step1 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (|(b─c)| = |(a─b)|) := by
  sorry

theorem routeB_refute_step1 :
    ∃ (a b c d e : Point) (AB BC AC : Line),
      formTriangle a b c AB BC AC ∧ |(a─b)| = |(a─c)| ∧
      between a b d ∧ between a c e ∧ ¬(|(b─c)| = |(a─b)|) := by
  obtain ⟨a, -⟩ := arbitrary_point
  obtain ⟨b, hab⟩ := distinct_points a
  obtain ⟨AB, haAB, hbAB⟩ := line_from_points a b hab
  have hdAB : distinctPointsOnLine a b AB := ⟨haAB, hbAB, hab⟩
  -- m between a and b
  obtain ⟨m, hmAB, hamb⟩ := exists_point_between_points_on_line AB a b hdAB
  have hbma : between b m a := (between_symm a m b hamb).1
  have hbm_ne : b ≠ m := (between_symm b m a hbma).2.1
  have ham_ne : a ≠ m := (between_symm a m b hamb).2.1
  -- circles α = (a, |ab|), γ = (b, |bm|)
  obtain ⟨α, hca_α, hob_α⟩ := circle_from_points a b hab
  obtain ⟨γ, hcb_γ, hom_γ⟩ := circle_from_points b m hbm_ne
  have haddb : |(a─m)| + |(m─b)| = |(a─b)| := between_if a m b hamb
  have ham_pos : (0:ℝ) < |(a─m)| := by
    by_contra h; push_neg at h
    have h0 : |(a─m)| = 0 := le_antisymm h (segment_gte_zero ⟨a, m⟩)
    exact ham_ne (zero_segment_if a m h0)
  have hmb_pos : (0:ℝ) < |(m─b)| := by
    by_contra h; push_neg at h
    have h0 : |(m─b)| = 0 := le_antisymm h (segment_gte_zero ⟨m, b⟩)
    exact hbm_ne.symm (zero_segment_if m b h0)
  have ham_lt : |(a─m)| < |(a─b)| := by linarith
  have hsymm_bm : |(b─m)| = |(m─b)| := segment_symmetric b m
  have hbm_lt_ab : |(b─m)| < |(a─b)| := by linarith
  have hminα : m.insideCircle α := point_in_circle_if a b m α ⟨hca_α, hob_α, ham_lt⟩
  have hbinγ : b.insideCircle γ := center_inside_circle b γ hcb_γ
  have hαγ : α.intersectsCircle γ :=
    intersection_circle_circle_2 b m α γ hob_α hminα hbinγ hom_γ
  obtain ⟨c, hc_α, hc_γ⟩ := intersection_circles α γ hαγ
  have hac : |(a─c)| = |(a─b)| := point_on_circle_onlyif a b c α ⟨hca_α, hob_α, hc_α⟩
  have hbc : |(b─c)| = |(b─m)| := point_on_circle_onlyif b m c γ ⟨hcb_γ, hom_γ, hc_γ⟩
  have hbc_ne : b ≠ c := by
    intro h
    have h0 : |(b─c)| = 0 := by rw [h]; exact zero_segment_onlyif c c rfl
    linarith
  have hca_ne : c ≠ a := by
    intro h; rw [h] at hac
    have h0 : |(a─b)| = 0 := by rw [← hac]; exact zero_segment_onlyif a a rfl
    exact hab (zero_segment_if a b h0)
  obtain ⟨BC, hbBC, hcBC⟩ := line_from_points b c hbc_ne
  obtain ⟨AC, hcAC, haAC⟩ := line_from_points c a hca_ne
  -- produce D beyond b on AB, E beyond c on AC
  obtain ⟨d, -, hbd⟩ := extend_point AB a b hdAB
  have hdAC : distinctPointsOnLine a c AC := ⟨haAC, hcAC, hca_ne.symm⟩
  obtain ⟨e, -, hce⟩ := extend_point AC a c hdAC
  refine ⟨a, b, c, d, e, AB, BC, AC, ?_, ?_, hbd, hce, ?_⟩
  · refine ⟨hdAB, hbBC, hcBC, hcAC, haAC, ?_⟩
    euclid_finish
  · linarith
  · linarith

#print axioms routeB_refute_step1

theorem proposition_5 : ∀ (a b c d e : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (|(a─b)| = |(a─c)|) ∧
  (between a b d) ∧ (between a c e) →
  (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.5.0"
    "For isosceles triangles, the angles at the base are equal to one another, and if the equal sides are produced then the angles under the base will be equal to one another. Let $ABC$ be an isosceles triangle having the side $AB$ equal to the side $AC$, and let the straight-lines $BD$ and $CE$ have been produced in a straight-line with $AB$ and $AC$ (respectively) [Post.~2]. I say that the angle $ABC$ is equal to $ACB$, and (angle) $CBD$  to $BCE$. "

  -- @assumption ("the side $AB$ is equal to the side $AC$", |(a─b)| = |(a─c)|)
  euclid_sentence "1.5.1"
    "Since the side $AB$ is equal to the side $AC$, and the base $AC$ is equal to the side $AB$, the side $BC$ is equal to the side $AB$. "
    (step1 : |(b─c)| = |(a─b)|) := by sorry

  -- @contradiction
  have contradiction : False := by
    obtain ⟨a', b', c', d', e', AB', BC', AC', hft, hab_ac, hbd, hce, hbc_ne⟩ :=
      routeB_refute_step1
    exact hbc_ne (proposition_5_step1 a' b' c' d' e' AB' BC' AC' ⟨hft, hab_ac, hbd, hce⟩)

  euclid_sentence "1.5.4"
    "Thus, the angles at the base are equal to one another, and the angles under the base are equal to one another."
    (step4 : (∠ a:b:c = ∠ a:c:b) ∧ (∠ c:b:d = ∠ b:c:e)) := by sorry

  exact step4
  euclid_conclude_sentence "1.5.5"
    "(Which is) the very thing it was required to show."

end Elements.Book1
