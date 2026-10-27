import SystemE

namespace Elements.Book3

theorem proposition_6 : ∀ (ABC CDE : Circle),
  -- "touch" = Def III.3 (meet but do not cut), NOT "exactly one point" (that is the later theorem
  -- III.13, which cites III.11 — defining touch as ∃! here would be circular). `ABC ≠ CDE` is the
  -- "two distinct circles" of the enunciation (same-circle satisfies meet+don't-cut, so it's needed).
  ABC ≠ CDE →
  (∃ c : Point, c.onCircle ABC ∧ c.onCircle CDE) ∧ ¬ ABC.intersectsCircle CDE →
  ¬ ∃ f : Point, f.isCentre ABC ∧ f.isCentre CDE := by
  sorry

end Elements.Book3
