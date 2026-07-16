import SystemE
import Book1.Prop20.Main
import Book1Variants.Prop22

namespace Elements.Book1

theorem proposition_23 : ∀ (a b c d e : Point) (AB CD CE : Line),
  distinctPointsOnLine a b AB ∧ formRectilinearAngle d c e CD CE →
  ∃ f : Point, f ≠ a ∧ (∠ f:a:b = ∠ d:c:e) := by
  euclid_intros
  euclid_intro_sentence "1.23.0"
    "To construct a rectilinear angle equal to a given rectilinear angle at a (given) point on a given straight-line. Let $AB$ be the given straight-line,  $A$ the (given) point on it, and  $DCE$ the given rectilinear angle. So it is required to construct a rectilinear angle equal to the given rectilinear angle $DCE$ at the (given) point $A$ on the given straight-line $AB$. "
  by_cases (d.onLine CE)
  -- Degenerate case omitted by Euclid
  ·
    by_cases (∠ d:c:e = 0)
    · use b; euclid_finish
    · euclid_assert ∠ d:c:e = ∟ + ∟
      euclid_apply (extend_point AB b a) as b'
      use b'; euclid_finish
  euclid_apply (line_from_points d e) as DE
  euclid_sentence "1.23.1"
    "Let the points $D$ and $E$ have been taken at random on each of the (straight-lines) $CD$ and $CE$ (respectively), and let $DE$ have been joined."
    (step1 : distinctPointsOnLine d e DE) := by sorry
  -- Euclid didn't explicitly apply proposition_20 (triangle inequality preconditions).
  euclid_apply (proposition_20 c d e CD DE CE)
  euclid_apply (proposition_20 d e c DE CE CD)
  euclid_apply (proposition_20 e c d CE CD DE)
  euclid_apply (proposition_22' c d c e e d a b CD CE DE AB) as (f, g)
  euclid_apply (line_from_points a f) as FA
  euclid_apply (line_from_points f g) as FG
  have hfoff : ¬f.onLine AB := by sorry
  euclid_sentence "1.23.2"
    "And let the triangle $AFG$ have been constructed from three straight-lines which are equal to $CD$, $DE$, and $CE$,"
    (step2 : formTriangle a f g FA FG AB) := by sorry
  euclid_sentence "1.23.3"
    "such that $CD$ is equal to $AF$,"
    (step3 : |(c─d)| = |(a─f)|) := by sorry
  euclid_sentence "1.23.4"
    "$CE$ to $AG$,"
    (step4 : |(c─e)| = |(a─g)|) := by sorry
  euclid_sentence "1.23.5"
    "and further $DE$ to $FG$ [Prop.~1.22]. "
    (step5 : |(d─e)| = |(f─g)|) := by sorry
  -- @assumption_valid
  have step6_assumption1 : |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)| := by euclid_finish
  -- @assumption_valid
  have step6_assumption2 : |(d─e)| = |(f─g)| := by assumption
  -- @assumption ("the two (straight-lines) $DC$, $CE$ are equal to the two (straight-lines) $FA$, $AG$, respectively", |(c─d)| = |(a─f)| ∧ |(c─e)| = |(a─g)|)
  -- @assumption ("the base $DE$ is equal to the base $FG$", |(d─e)| = |(f─g)|)
  euclid_sentence "1.23.6"
    "Therefore, since the two (straight-lines) $DC$, $CE$ are equal to the two (straight-lines) $FA$, $AG$, respectively, and the base $DE$ is equal to the base $FG$, the angle $DCE$ is thus equal to the angle $FAG$ [Prop.~1.8]. "
    (step6 : ∠ d:c:e = ∠ f:a:g) := by sorry
  use f
  have hfa : f ≠ a := by sorry
  have hangle : ∠ f:a:b = ∠ d:c:e := by sorry
  exact ⟨hfa, hangle⟩
  euclid_conclude_sentence "1.23.7"
    "Thus, the rectilinear angle $FAG$,  equal to the  given rectilinear angle $DCE$, has been constructed at the (given) point $A$ on the given straight-line $AB$. (Which is) the very thing it was required to do."

end Elements.Book1
