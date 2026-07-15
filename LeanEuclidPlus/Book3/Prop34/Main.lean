import SystemE
import Book1.Prop23.Main
import Book3.Prop32.Main

namespace Elements.Book3

open Elements.Book1

theorem proposition_34 : ∀ (ABC : Circle) (d1 d d2 : Point),
  d1 ≠ d ∧ d2 ≠ d →
  0 < ∠ d1:d:d2 → ∠ d1:d:d2 < ∟ + ∟ →
  ∃ (b c : Point), b.onCircle ABC ∧ c.onCircle ABC ∧ b ≠ c ∧
    ∃ a : Point, a.onCircle ABC ∧ ∠ b:a:c = ∠ d1:d:d2 :=
by
  euclid_intros
  euclid_intro_sentence "3.34.0"
    "To cut off a segment, accepting an angle equal to a given rectilinear angle, from a given circle. Let $ABC$ be the given circle, and $D$ the given rectilinear angle. So it is required to cut off a segment, accepting an angle equal to the given rectilinear angle $D$, from the given circle $ABC$."

  -- Get b on the circle ABC (tangent contact point)
  obtain ⟨b, hb_ABC⟩ := exists_point_on_circle ABC
  -- Tangent line EF at b, plus: every other line through b meets ABC (Porism to III.16)
  have hEF_exists : ∃ EF : Line, b.onLine EF ∧ ¬ EF.intersectsCircle ABC ∧
      (∀ FA : Line, b.onLine FA → FA ≠ EF → FA.intersectsCircle ABC) := by sorry
  obtain ⟨EF, hb_EF, hEF_notint, hEF_others⟩ := hEF_exists

  euclid_sentence "3.34.1"
    "Let $EF$ be drawn touching $ABC$ at point $B$.$^\\dag$"
    (step1 : b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC) := by sorry

  -- Two points p, q straddling b on the tangent EF (e, f named later by side)
  have hpq : ∃ p q : Point, p.onLine EF ∧ q.onLine EF ∧ between p b q := by sorry
  obtain ⟨p, q, hp_EF, hq_EF, hbet_pbq⟩ := hpq
  -- angle QBC₀ = D at B on the straight-line QB [Prop 1.23]
  euclid_apply (line_from_points d d1) as DD1
  euclid_apply (line_from_points d d2) as DD2
  euclid_apply (proposition_23 b q d d1 d2 EF DD1 DD2) as c₀
  have hbc₀ne : b ≠ c₀ := by euclid_finish
  -- Line BC through b and c₀ (the chord direction)
  euclid_apply (line_from_points b c₀) as BC
  -- BC is not the tangent, hence it meets the circle again
  have hBC_int : BC.intersectsCircle ABC := by sorry
  -- the far intersection c of chord BC with ABC (distinct from b)
  have hc_ex : ∃ c : Point, c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c := by sorry
  obtain ⟨c, hc_ABC, hc_BC, hbc_ne⟩ := hc_ex
  -- name e, f from {p, q} so that ∠ f:b:c = D (uses the p/q straddle symmetry)
  have hef_choice : ∃ e f : Point, e.onLine EF ∧ f.onLine EF ∧ between e b f ∧
      ∠ f:b:c = ∠ d1:d:d2 := by sorry
  obtain ⟨e, f, he_EF, hf_EF, hbet_ebf, hangle_fbc⟩ := hef_choice

  euclid_sentence "3.34.2"
    "And let (angle) $FBC$, equal to angle $D$, be constructed on the straight-line $FB$, at the point $B$ on it [Prop.~1.23]."
    (step2 : ∠ f:b:c = ∠ d1:d:d2) := by sorry

  -- Get a in the alternate segment BAC (on ABC, opposite side of BC from f)
  have ha_exists : ∃ a : Point, a.onCircle ABC ∧ a.opposingSides f BC := by sorry
  obtain ⟨a, ha_ABC, ha_opp⟩ := ha_exists

  -- @assumption_valid
  have step3_assumption1 : b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC := by euclid_finish
  -- @assumption_gap
  have step3_assumption2 : b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c := by sorry
  -- @suppress_deps_check "source cites [Prop.~1.32] (exterior-angle) but this is the alternate-segment theorem, Euclid III.32 = proposition_32"
  -- @assumption ("some straight-line $EF$ touches the circle $ABC$", b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC)
  -- @assumption ("$BC$ has been drawn across (the circle) from the point of contact $B$", b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c)
  euclid_sentence "3.34.3"
    "Therefore, since some straight-line $EF$ touches the circle $ABC$, and $BC$ has been drawn across (the circle) from the point of contact $B$, angle $FBC$ is thus equal to the angle constructed in the alternate segment $BAC$ [Prop.~1.32]."
    (step3 : ∠ f:b:c = ∠ b:a:c) := by sorry

  euclid_sentence "3.34.4"
    "But, $FBC$ is equal to $D$."
    (step4 : ∠ f:b:c = ∠ d1:d:d2) := by sorry

  euclid_sentence "3.34.5"
    "Thus, the (angle) in the segment $BAC$ is also equal to [angle] $D$."
    (step5 : ∠ b:a:c = ∠ d1:d:d2) := by sorry

  refine ⟨b, c, hb_ABC, hc_ABC, hbc_ne, ?_⟩
  exact ⟨a, ha_ABC, step5⟩
  euclid_conclude_sentence "3.34.6"
    "Thus, the segment $BAC$, accepting an angle equal to the given rectilinear angle $D$, has been cut off from the given circle $ABC$. (Which is) the very thing it was required to do."

end Elements.Book3
