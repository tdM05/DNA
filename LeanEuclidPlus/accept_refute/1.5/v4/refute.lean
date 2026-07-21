import SystemE
import Mathlib.Tactic.Linarith

set_option systemE.solverTime 30
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

/-! v4 — ROUTE B refutation of the equilateral bad step `|(b─c)| = |(a─b)|` (step1).

    This is the case that was previously "stuck": the step is mixed (true for an equilateral
    triangle, false otherwise), so the naive refute `H → ¬(|(b─c)| = |(a─b)|)` FAILS, and the
    countermodel needs a NON-equilateral isosceles triangle — which `euclid_finish` cannot
    synthesise. We build that countermodel by hand from the raw construction axioms:

      m between a,b; α = circle(a, |ab|); γ = circle(b, |bm|); c = α ∩ γ
        ⟹ |ac| = |ab|  and  |bc| = |bm| < |ab|   (since |am| > 0)

    so `c` is isosceles-with-vertex-a but strictly short-based: `|bc| ≠ |ab|`. Producing D, E
    completes the I.5 config. By soundness, System E cannot deduce the equilateral step.
    Axiom-clean (no sorryAx — see `#print axioms`). -/

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

end Elements.Book1
