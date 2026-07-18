import SystemE
import Book1.Prop04.Main
import Book1.Prop05.Main
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book1.Prop13.Main
import Book1.Prop23.Main
import Book1.Prop32.Main
import Book3.Prop16.Main
import Book3.Prop32.Main
import Mathlib.Tactic.Linarith

set_option systemE.solverTime 60
set_option maxHeartbeats 1000000

namespace Elements.Book3

open Elements.Book1

theorem proposition_33 : ∀ (a b c₁ c c₂ : Point),
  a ≠ b →
  c₁ ≠ c → c ≠ c₂ →
  0 < ∠ c₁:c:c₂ → ∠ c₁:c:c₂ < ∟ + ∟ →
  ∃ (α : Circle) (e : Point), a.onCircle α ∧ b.onCircle α ∧ e.onCircle α ∧ ∠ a:e:b = ∠ c₁:c:c₂ :=
by
  euclid_intros
  euclid_intro_sentence "3.33.0"
    "To draw a segment of a circle, accepting an angle equal to a given rectilinear angle, on a given straight-line. Let $AB$ be the given straight-line, and $C$ the given rectilinear angle. So it is required to draw a segment of a circle, accepting an angle equal to $C$, on the given straight-line $AB$. So the [angle] $C$ is surely either acute, a right-angle, or obtuse. First of all, let it be acute."

  rcases lt_trichotomy (∠ c₁:c:c₂) ∟ with hacute | hright | hobtuse

  -- ── CASE 1 : ∠ c₁:c:c₂ < ∟  (acute) ─────────────────────────────────────────
  ·
    have hnrt : ∠ c₁:c:c₂ ≠ ∟ := ne_of_lt hacute
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = angle C at A on AB [Prop 1.23]
    euclid_apply (line_from_points c c₁) as CC1
    euclid_apply (line_from_points c c₂) as CC2
    euclid_apply (proposition_23 a b c c₁ c₂ AB CC1 CC2) as d
    euclid_apply (line_from_points a d) as AD
    -- AE at right-angles to DA at A [Prop 1.11]: extend AD past A, erect ⊥ at A (direction e0)
    euclid_apply (extend_point AD d a) as d0
    euclid_apply (proposition_11 d d0 a AD) as e0
    euclid_apply (line_from_points a e0) as AE
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    -- FG at right-angles to AB at F [Prop 1.11]; G = FG ∩ AE (centre of the circle)
    euclid_apply (proposition_11 a b f AB) as g0
    euclid_apply (line_from_points f g0) as FG
    -- FG ⊥ AB and AE ⊥ AD meet: AB is a transversal crossing FG at F and AE at A.  On the side of AB
    -- where the two perpendiculars converge, the interior angles sum to less than two right-angles
    -- (∟ at F and < ∟ at A, since ∠DAB ≠ ∟), so by Euclid's fifth postulate FG and AE meet there.  We
    -- pick the perpendicular feet GG on FG and QE on AE on that (single) convergent side of AB.
    euclid_apply (extend_point AE e0 a) as e0'
    euclid_apply (extend_point FG g0 f) as g0'
    have hFG_int_AE : FG.intersectsLine AE := by
      -- Feet of the two perpendiculars on the side of AB opposite D (∠DAB acute ⇒ centre there).
      obtain ⟨gg, hgg_on, hgg_s⟩ : ∃ gg : Point, gg.onLine FG ∧ gg.opposingSides d AB := by
        by_cases h : g0.opposingSides d AB
        · exact ⟨g0, by euclid_finish, h⟩
        · exact ⟨g0', by euclid_finish, by euclid_finish⟩
      obtain ⟨qe, hqe_on, hqe_s⟩ : ∃ qe : Point, qe.onLine AE ∧ qe.opposingSides d AB := by
        by_cases h : e0.opposingSides d AB
        · exact ⟨e0, by euclid_finish, h⟩
        · exact ⟨e0', by euclid_finish, by euclid_finish⟩
      -- B is on D's side of AE: otherwise segment DB crosses AE at a point P (between D and B), and
      -- since ∠DAP = ∟ (P on AE ⊥ AD) with ray AP inside ∠DAB, we get ∠DAB = ∟ + ∠PAB ≥ ∟, absurd.
      have hd_b_ae : d.sameSide b AE := by
        by_contra hc
        have hopp : d.opposingSides b AE := ⟨by euclid_finish, by euclid_finish, hc⟩
        euclid_apply (line_from_points d b) as DB
        euclid_apply (intersection_lines AE DB) as pcr
        have hbtw : between d pcr b := by euclid_finish
        have hperp : ∠ d:a:pcr = ∟ := by euclid_finish
        have hss1 : d.sameSide pcr AB := by euclid_finish
        have hss2 : b.sameSide pcr AD := by euclid_finish
        have hsplit : ∠ d:a:b = ∠ d:a:pcr + ∠ pcr:a:b := by euclid_finish
        euclid_finish
      have hqe_b_ad : qe.sameSide b AD := by euclid_finish
      have hsum : ∠ gg:f:a + ∠ f:a:qe < ∟ + ∟ := by euclid_finish
      euclid_apply (lines_intersect gg f a qe FG AB AE)
      euclid_finish
    euclid_apply (intersection_lines FG AE) as g
    have hga : g ≠ a := by euclid_finish
    euclid_apply (circle_from_points g a) as α
    -- E = the far end of diameter AE (on the circle, since centre G lies on AE)
    euclid_apply (intersection_circle_line_extending_points α AE g a) as e
    have hgb : g ≠ b := by euclid_finish
    euclid_apply (line_from_points g b) as GB
    euclid_apply (line_from_points a g) as AG
    -- B also lies on this circle (proved via AG = BG from SAS)
    have hb_circ : b.onCircle α := by
      euclid_apply (Elements.Book1.proposition_4 f a g f b g AB AG FG AB GB FG)
      euclid_finish
    -- EB joined
    have heb : e ≠ b := by euclid_finish
    euclid_apply (line_from_points e b) as EB
    -- AD touches α at A [Prop.~3.16 corr.]; the circle therefore lies entirely on one side of AD, so
    -- the centre G and the chord end B are on the same side of AD. Combined with ∠DAG = ∟ and the
    -- acute ∠DAB, this puts G — and hence its antipode E of A — on the opposite side of AB from D.
    have htang : ¬ AD.intersectsCircle α := by
      euclid_apply (Elements.Book3.proposition_16 a e g d α AD)
      euclid_finish
    have hg_sb_ad : g.sameSide b AD := by euclid_finish
    have hg_od : g.opposingSides d AB := by euclid_finish
    have he_od : e.opposingSides d AB := by euclid_finish
    -- The 4th vertex of the cyclic quadrilateral needed by [Prop.~3.32]: a circle point on the D side
    -- of AB. FG passes through the centre G, so it is a diameter, meeting α on both sides of AB.
    have hFGcirc1 : FG.intersectsCircle α := by euclid_finish
    euclid_apply (intersections_circle_line α FG) as (cc1, cc2)
    have hcpt : ∃ cpt : Point, cpt.onCircle α ∧ cpt.opposingSides d0 AB := by
      by_cases hcc : cc1.opposingSides d0 AB
      · exact ⟨cc1, by euclid_finish, hcc⟩
      · exact ⟨cc2, by euclid_finish, by euclid_finish⟩
    obtain ⟨cpt, hcpt_circ, hcpt_side⟩ := hcpt

    euclid_sentence "3.33.1"
      "And, as in the first diagram (from the left), let (angle) $BAD$, equal to angle $C$, be constructed on the straight-line $AB$, at the point A (on it) [Prop.~1.23]."
      (step1 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.2"
      "Thus, $BAD$ is also acute."
      (step2 : ∠ b:a:d < ∟) := by euclid_finish

    euclid_sentence "3.33.3"
      "Let $AE$ be drawn, at right-angles to $DA$ [Prop.~1.11]."
      (step3 : ∠ d:a:e = ∟) := by euclid_finish

    euclid_sentence "3.33.4"
      "And let $AB$ be cut in half at $F$ [Prop.~1.10]."
      (step4 : between a f b ∧ |(a─f)| = |(f─b)|) := by euclid_finish

    euclid_sentence "3.33.5"
      "And let $FG$ be drawn from point $F$, at right-angles to $AB$ [Prop.~1.11]."
      (step5 : ∠ a:f:g = ∟) := by euclid_finish

    euclid_sentence "3.33.6"
      "And let $GB$ be joined."
      (step6 : distinctPointsOnLine g b GB) := by euclid_finish

    -- @assumption_valid
    have step7_assumption1 : |(a─f)| = |(f─b)| := by assumption
    -- @assumption_valid
    have step7_assumption2 : |(f─g)| = |(f─g)| := by rfl
    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FG$ (is) common", |(f─g)| = |(f─g)|)
    euclid_sentence "3.33.7"
      "And since $AF$ is equal to $FB$, and $FG$ (is) common, the two (straight-lines) $AF$, $FG$ are equal to the two (straight-lines) $BF$, $FG$ (respectively)."
      (step7 : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)|) := by
      refine (fun h1 h2 => ?_) step7_assumption1 step7_assumption2
      euclid_finish

    euclid_sentence "3.33.8"
      "And angle $AFG$ (is) equal to [angle] $BFG$."
      (step8 : ∠ a:f:g = ∠ b:f:g) := by euclid_finish

    euclid_sentence "3.33.9"
      "Thus, the base $AG$ is equal to the base $BG$ [Prop.~1.4]."
      (step9 : |(a─g)| = |(b─g)|) := by
      euclid_apply (Elements.Book1.proposition_4 f a g f b g AB AG FG AB GB FG)
      euclid_finish

    euclid_sentence "3.33.10"
      "Thus, the circle drawn with center $G$, and radius $GA$, will also go through $B$ (as well as $A$)."
      (step10 : a.onCircle α ∧ b.onCircle α) := by euclid_finish

    euclid_sentence "3.33.11"
      "Let it be drawn, and let it be (denoted) $ABE$."
      (step11 : g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ e.onCircle α) := by euclid_finish

    euclid_sentence "3.33.12"
      "And let $EB$ be joined."
      (step12 : distinctPointsOnLine e b EB) := by euclid_finish

    -- @assumption_valid
    have step13_assumption1 : ∠ d:a:e = ∟ := by assumption
    -- @assumption ("$AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$", ∠ d:a:e = ∟)
    euclid_sentence "3.33.13"
      "Therefore, since $AD$ is at the extremity of diameter $AE$, (namely, point) $A$, at right-angles to $AE$, the (straight-line) $AD$ thus touches the circle $ABE$ [Prop.~3.16~corr.]."
      (step13 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by
      refine (fun h => ?_) step13_assumption1
      euclid_apply (Elements.Book3.proposition_16 a e g d α AD)
      euclid_finish

    -- @assumption_valid
    have step14_assumption1 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α := by assumption
    -- @assumption_valid
    have step14_assumption2 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α := by euclid_finish
    -- @assumption ("some straight-line $AD$ touches the circle $ABE$", (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α)
    -- @assumption ("some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$", a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)
    euclid_sentence "3.33.14"
      "Therefore, since some straight-line $AD$ touches the circle $ABE$, and some (other) straight-line $AB$ has been drawn across from the point of contact $A$ into circle $ABE$, angle $DAB$ is thus equal to the angle $AEB$ in the alternate segment of the circle [Prop.~3.32]."
      (step14 : ∠ d:a:b = ∠ a:e:b) := by
      refine (fun h1 h2 => ?_) step14_assumption1 step14_assumption2
      euclid_apply (Elements.Book3.proposition_32 a e b cpt d0 d α AD AB)
      euclid_finish

    euclid_sentence "3.33.15"
      "But, $DAB$ is equal to $C$."
      (step15 : ∠ d:a:b = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.16"
      "Thus, angle $C$ is also equal to $AEB$."
      (step16 : ∠ c₁:c:c₂ = ∠ a:e:b) := by euclid_finish

    euclid_sentence "3.33.17"
      "Thus, a segment $AEB$ of a circle, accepting the angle $AEB$ (which is) equal to the given (angle) $C$, has been drawn on the given straight-line $AB$."
      (step17 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by
      refine ⟨α, e, ?_, ?_, ?_, ?_⟩ <;> euclid_finish

    exact step17

  -- ── CASE 2 : ∠ c₁:c:c₂ = ∟  (right angle) ─────────────────────────────────────
  ·
    euclid_wts "3.33.18"
      "And so let $C$ be a right-angle. And let it again be necessary to draw a segment of a circle on $AB$, accepting an angle equal to the right-[angle] $C$."

    -- Construction witnesses
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = right-angle C at A on AB [Prop 1.23]
    euclid_apply (line_from_points c c₁) as CC1
    euclid_apply (line_from_points c c₂) as CC2
    euclid_apply (proposition_23 a b c c₁ c₂ AB CC1 CC2) as d
    euclid_apply (line_from_points a d) as AD
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    have hfa : f ≠ a := by euclid_finish
    -- Circle AEB with center F, radius FA (= FB since F is midpoint)
    euclid_apply (circle_from_points f a) as α
    have hb_circ_2 : b.onCircle α := by euclid_finish
    -- E: a point on circle α not on AB (perpendicular to AB at centre F meets the circle)
    euclid_apply (proposition_11 a b f AB) as g0
    euclid_apply (line_from_points f g0) as FG
    euclid_apply (intersection_circle_line_extending_points α FG f g0) as e
    have he_off : ¬ e.onLine AB := by euclid_finish

    euclid_sentence "3.33.19"
      "Let the (angle) $BAD$ [again] be constructed, equal to the right-angle $C$ [Prop.~1.23], as in the second diagram (from the left)."
      (step19 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.20"
      "And let $AB$ be cut in half at $F$ [Prop.~1.10]."
      (step20 : between a f b ∧ |(a─f)| = |(f─b)|) := by euclid_finish

    euclid_sentence "3.33.21"
      "And let the circle $AEB$ be drawn with center $F$, and radius either $FA$ or $FB$."
      (step21 : f.isCentre α ∧ a.onCircle α ∧ b.onCircle α) := by euclid_finish

    -- @assumption_valid
    have step22_assumption1 : ∠ b:a:d = ∟ := by linarith
    -- @assumption ("the angle at $A$ being a right-angle", ∠ b:a:d = ∟)
    euclid_sentence "3.33.22"
      "Thus, the straight-line $AD$ touches the circle $ABE$, on account of the angle at $A$ being a right-angle [Prop.~3.16 corr.]."
      (step22 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by
      refine (fun h => ?_) step22_assumption1
      euclid_apply (Elements.Book3.proposition_16 a b f d α AD)
      euclid_finish

    -- Angle in a semi-circle is right: F is the centre and the midpoint of diameter AB, with E on
    -- the circle. Triangles FAE and FBE are isosceles (radii FA = FE = FB), so by [Prop.~1.5] the
    -- base angles are equal, and by [Prop.~1.32] the angles of triangle AEB sum to two right-angles.
    have hsemi : ∠ a:e:b = ∟ := by
      euclid_apply (line_from_points a e) as AElem
      euclid_apply (line_from_points e b) as EBlem
      euclid_apply (extend_point AB f a) as pa
      euclid_apply (extend_point AB f b) as pb
      euclid_apply (extend_point FG f e) as pe
      euclid_apply (extend_point EBlem e b) as pbb
      euclid_apply (Elements.Book1.proposition_5 f a e pa pe AB AElem FG)
      euclid_apply (Elements.Book1.proposition_5 f b e pb pe AB EBlem FG)
      euclid_apply (Elements.Book1.proposition_32 a e b pbb AElem EBlem AB)
      euclid_finish
    -- @suppress_deps_check "III.31 is skipped (its horn-angle segment addendum is not formalizable in System E); the semicircle right angle is re-derived in step23_assumption1 from I.5 + I.32 (as in Book3/Prop32/step6)."
    -- @assumption_gap
    have step23_assumption1 : ∠ a:e:b = ∟ := by exact hsemi
    -- @assumption ("(the latter angle), being in a semi-circle, is also a right-angle", ∠ a:e:b = ∟)
    euclid_sentence "3.33.23"
      "And angle $BAD$ is equal to the angle in segment $AEB$. For (the latter angle), being in a semi-circle, is also a right-angle [Prop.~3.31]."
      (step23 : ∠ b:a:d = ∠ a:e:b) := by
      refine (fun h => ?_) step23_assumption1
      euclid_finish

    euclid_sentence "3.33.24"
      "But, $BAD$ is also equal to $C$."
      (step24 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.25"
      "Thus, the (angle) in (segment) $AEB$ is also equal to $C$."
      (step25 : ∠ a:e:b = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.26"
      "Thus, a segment $AEB$ of a circle, accepting an angle equal to $C$, has again been drawn on $AB$."
      (step26 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by
      refine ⟨α, e, ?_, ?_, ?_, ?_⟩ <;> euclid_finish

    exact step26

  -- ── CASE 3 : ∟ < ∠ c₁:c:c₂  (obtuse) ─────────────────────────────────────────
  ·
    have hnrt : ∠ c₁:c:c₂ ≠ ∟ := (ne_of_lt hobtuse).symm
    euclid_wts "3.33.27"
      "And so let (angle) $C$ be obtuse."

    -- Construction witnesses
    euclid_apply (line_from_points a b) as AB
    -- angle BAD = obtuse angle C at A on AB [Prop 1.23]
    euclid_apply (line_from_points c c₁) as CC1
    euclid_apply (line_from_points c c₂) as CC2
    euclid_apply (proposition_23 a b c c₁ c₂ AB CC1 CC2) as d
    euclid_apply (line_from_points a d) as AD
    -- AE at right-angles to AD at A [Prop 1.11]: extend AD past A, erect ⊥ at A (direction e0)
    euclid_apply (extend_point AD d a) as d0
    euclid_apply (proposition_11 d d0 a AD) as e0
    euclid_apply (line_from_points a e0) as AE
    -- AB bisected at F [Prop 1.10]
    euclid_apply (proposition_10 a b AB) as f
    -- FG at right-angles to AB at F [Prop 1.11]; G = FG ∩ AE (centre of the circle)
    euclid_apply (proposition_11 a b f AB) as g0
    euclid_apply (line_from_points f g0) as FG
    euclid_apply (extend_point AE e0 a) as e0'
    euclid_apply (extend_point FG g0 f) as g0'
    have hFG_int_AE : FG.intersectsLine AE := by
      -- Obtuse mirror of the acute case: work with D0 (the far ray of AD), for which ∠D0AB is acute.
      have hlin : ∠ d:a:b + ∠ d0:a:b = ∟ + ∟ := by
        euclid_apply (Elements.Book1.proposition_13 b a d d0 AB AD)
        euclid_finish
      have hd0acute : ∠ d0:a:b < ∟ := by euclid_finish
      -- Feet of the two perpendiculars on the side of AB opposite D0 (= D's side, where the centre is).
      obtain ⟨gg, hgg_on, hgg_s⟩ : ∃ gg : Point, gg.onLine FG ∧ gg.opposingSides d0 AB := by
        by_cases h : g0.opposingSides d0 AB
        · exact ⟨g0, by euclid_finish, h⟩
        · exact ⟨g0', by euclid_finish, by euclid_finish⟩
      obtain ⟨qe, hqe_on, hqe_s⟩ : ∃ qe : Point, qe.onLine AE ∧ qe.opposingSides d0 AB := by
        by_cases h : e0.opposingSides d0 AB
        · exact ⟨e0, by euclid_finish, h⟩
        · exact ⟨e0', by euclid_finish, by euclid_finish⟩
      have hd_b_ae : d0.sameSide b AE := by
        by_contra hc
        have hopp : d0.opposingSides b AE := ⟨by euclid_finish, by euclid_finish, hc⟩
        euclid_apply (line_from_points d0 b) as DB
        euclid_apply (intersection_lines AE DB) as pcr
        have hbtw : between d0 pcr b := by euclid_finish
        have hperp : ∠ d0:a:pcr = ∟ := by euclid_finish
        have hss1 : d0.sameSide pcr AB := by euclid_finish
        have hss2 : b.sameSide pcr AD := by euclid_finish
        have hsplit : ∠ d0:a:b = ∠ d0:a:pcr + ∠ pcr:a:b := by euclid_finish
        euclid_finish
      have hqe_b_ad : qe.sameSide b AD := by euclid_finish
      have hqperp : ∠ d0:a:qe = ∟ := by euclid_finish
      have hsplit2 : ∠ d0:a:qe = ∠ d0:a:b + ∠ b:a:qe := by euclid_finish
      have hd0pos : (0:ℝ) < ∠ d0:a:b := by euclid_finish
      have hfaqe : ∠ f:a:qe = ∠ b:a:qe := by euclid_finish
      have hggperp : ∠ gg:f:a = ∟ := by euclid_finish
      have hsum : ∠ gg:f:a + ∠ f:a:qe < ∟ + ∟ := by euclid_finish
      euclid_apply (lines_intersect gg f a qe FG AB AE)
      euclid_finish
    euclid_apply (intersection_lines FG AE) as g
    have hga : g ≠ a := by euclid_finish
    have hgb : g ≠ b := by euclid_finish
    euclid_apply (line_from_points g b) as GB
    euclid_apply (line_from_points a g) as AG
    -- Circle with center G, radius GA
    euclid_apply (circle_from_points g a) as α
    have hb_circ : b.onCircle α := by
      euclid_apply (Elements.Book1.proposition_4 f a g f b g AB AG FG AB GB FG)
      euclid_finish
    -- H: a point on the circle in the alternate segment AHB (opposite side of AB from D). FG (through
    -- centre g) is a diameter, so it meets α at two points straddling AB at the interior point f; pick
    -- the one on the far side of AB from d.
    have hFGcirc : FG.intersectsCircle α := by euclid_finish
    euclid_apply (intersections_circle_line α FG) as (h1, h2)
    have hh_straddle : h1.opposingSides h2 AB := by euclid_finish
    -- h is the inscribed point opposite d (alternate segment); h' the other FG∩α point, opposite d0.
    have hh_ex : ∃ hh hh' : Point, hh.onCircle α ∧ hh.opposingSides d AB ∧
        hh'.onCircle α ∧ hh'.opposingSides d0 AB := by
      by_cases hd1 : h1.opposingSides d AB
      · exact ⟨h1, h2, by euclid_finish, hd1, by euclid_finish, by euclid_finish⟩
      · exact ⟨h2, h1, by euclid_finish, by euclid_finish, by euclid_finish, by euclid_finish⟩
    obtain ⟨h, h', hh_circ, hh_side, hh'_circ, hh'_side⟩ := hh_ex

    euclid_sentence "3.33.28"
      "And let (angle) $BAD$, equal to ($C$), be constructed on the straight-line $AB$, at the point $A$ (on it) [Prop.~1.23], as in the third diagram (from the left)."
      (step28 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.29"
      "And let $AE$ be drawn, at right-angles to $AD$ [Prop.~1.11]."
      (step29 : ∠ d:a:e0 = ∟) := by euclid_finish

    euclid_sentence "3.33.30"
      "And let $AB$ again be cut in half at $F$ [Prop.~1.10]."
      (step30 : between a f b ∧ |(a─f)| = |(f─b)|) := by euclid_finish

    euclid_sentence "3.33.31"
      "And let $FG$ be drawn, at right-angles to $AB$ [Prop.~1.10]."
      (step31 : ∠ a:f:g = ∟) := by euclid_finish

    euclid_sentence "3.33.32"
      "And let $GB$ be joined."
      (step32 : distinctPointsOnLine g b GB) := by euclid_finish

    -- @assumption_valid
    have step33_assumption1 : |(a─f)| = |(f─b)| := by assumption
    -- @assumption_valid
    have step33_assumption2 : |(f─g)| = |(f─g)| := by rfl
    -- @assumption ("$AF$ is equal to $FB$", |(a─f)| = |(f─b)|)
    -- @assumption ("$FG$ (is) common", |(f─g)| = |(f─g)|)
    euclid_sentence "3.33.33"
      "And again, since $AF$ is equal to $FB$, and $FG$ (is) common, the two (straight-lines) $AF$, $FG$ are equal to the two (straight-lines) $BF$, $FG$ (respectively)."
      (step33 : |(a─f)| = |(b─f)| ∧ |(f─g)| = |(f─g)|) := by
      refine (fun hx hy => ?_) step33_assumption1 step33_assumption2
      euclid_finish

    euclid_sentence "3.33.34"
      "And angle $AFG$ (is) equal to angle $BFG$."
      (step34 : ∠ a:f:g = ∠ b:f:g) := by euclid_finish

    euclid_sentence "3.33.35"
      "Thus, the base $AG$ is equal to the base $BG$ [Prop.~1.4]."
      (step35 : |(a─g)| = |(b─g)|) := by
      euclid_apply (Elements.Book1.proposition_4 f a g f b g AB AG FG AB GB FG)
      euclid_finish

    euclid_sentence "3.33.36"
      "Thus, a circle of center $G$, and radius $GA$, being drawn, will also go through $B$ (as well as $A$)."
      (step36 : a.onCircle α ∧ b.onCircle α) := by euclid_finish

    euclid_sentence "3.33.37"
      "Let it go like $AEB$ (in the third diagram from the left)."
      (step37 : g.isCentre α ∧ a.onCircle α ∧ b.onCircle α ∧ h.onCircle α) := by euclid_finish

    -- @assumption_valid
    have step38_assumption1 : ∠ d:a:e0 = ∟ := by assumption
    -- @assumption ("$AD$ is at right-angles to the diameter $AE$, at its extremity", ∠ d:a:e0 = ∟)
    euclid_sentence "3.33.38"
      "And since $AD$ is at right-angles to the diameter $AE$, at its extremity, $AD$ thus touches circle $AEB$ [Prop.~3.16~corr.]."
      (step38 : (∃ p : Point, p.onLine AD ∧ p.onCircle α) ∧ ¬ AD.intersectsCircle α) := by
      refine (fun hyp => ?_) step38_assumption1
      euclid_apply (intersection_circle_line_extending_points α AE g a) as ee
      euclid_apply (Elements.Book3.proposition_16 a ee g d α AD)
      euclid_finish

    -- @assumption_valid
    have step39_assumption1 : a.onLine AB ∧ b.onLine AB ∧ b.onCircle α := by euclid_finish
    -- @assumption ("$AB$ has been drawn across (the circle) from the point of contact $A$", a.onLine AB ∧ b.onLine AB ∧ b.onCircle α)
    euclid_sentence "3.33.39"
      "And $AB$ has been drawn across (the circle) from the point of contact $A$. Thus, angle $BAD$ is equal to the angle constructed in the alternate segment $AHB$ of the circle [Prop.~3.32]."
      (step39 : ∠ b:a:d = ∠ a:h:b) := by
      refine (fun hyp => ?_) step39_assumption1
      euclid_apply (Elements.Book3.proposition_32 a h b h' d0 d α AD AB)
      euclid_finish

    euclid_sentence "3.33.40"
      "But, angle $BAD$ is equal to $C$."
      (step40 : ∠ b:a:d = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.41"
      "Thus, the angle in segment $AHB$ is also equal to $C$."
      (step41 : ∠ a:h:b = ∠ c₁:c:c₂) := by euclid_finish

    euclid_sentence "3.33.42"
      "Thus, a segment $AHB$ of a circle, accepting an angle equal to $C$, has been drawn on the given straight-line $AB$."
      (step42 : ∃ (β : Circle) (p : Point), a.onCircle β ∧ b.onCircle β ∧ p.onCircle β ∧ ∠ a:p:b = ∠ c₁:c:c₂) := by
      refine ⟨α, h, ?_, ?_, ?_, ?_⟩ <;> euclid_finish

    exact step42

  euclid_conclude_sentence "3.33.43"
    "(Which is) the very thing it was required to do."

end Elements.Book3
