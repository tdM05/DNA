import SystemE

namespace Elements.Book3

theorem proposition_5 : ∀ (ABC CDG : Circle),
  -- "two circles" of the enunciation: distinct (System E does NOT forbid a circle intersecting
  -- itself, so without this ABC = CDG satisfies the hypothesis and the statement is false).
  ABC ≠ CDG →
  ABC.intersectsCircle CDG →
  ¬ ∃ e : Point, e.isCentre ABC ∧ e.isCentre CDG := by
  sorry

end Elements.Book3
