import SystemE

namespace Elements.Book3

-- Faithful to Euclid's DEMONSTRATION (not the enunciation's "always"): he names the three other lines
-- FB, FC, FG and proves the specific chain FA>FB>FC>FG>FD (greatest/least = the ends of the chain), under
-- the figure ordering ∠BEF>∠CEF>∠GEF; plus the two-equal (a mirror H on the far side of AD, and uniqueness).
-- Modeled on the faithful sibling Book3/Prop08. (The earlier ∀-over-all-points version over-generalized
-- beyond what the proof actually demonstrates — corrected 2026-07-06.)
theorem proposition_7 : ∀ (ABCD : Circle) (a d e f b c g : Point) (AD : Line),
  e.isCentre ABCD →
  a.onCircle ABCD →
  d.onCircle ABCD →
  distinctPointsOnLine a d AD →
  between a e d →
  between e f d →
  b.onCircle ABCD →
  c.onCircle ABCD →
  g.onCircle ABCD →
  -- Non-degeneracy: b, c, g are not the endpoints of the diameter
  b ≠ a → b ≠ d →
  c ≠ a → c ≠ d →
  g ≠ a → g ≠ d →
  ∠ b:e:f > ∠ c:e:f →
  ∠ c:e:f > ∠ g:e:f →
  |(f─a)| > |(f─b)| ∧
  |(f─b)| > |(f─c)| ∧
  |(f─c)| > |(f─g)| ∧
  |(f─g)| > |(f─d)| ∧
  (∃ h : Point, h.onCircle ABCD ∧ h.opposingSides g AD ∧ |(f─h)| = |(f─g)| ∧
    ∀ n : Point, n.onCircle ABCD → |(f─n)| = |(f─g)| → n = g ∨ n = h) := by
  sorry

end Elements.Book3
