import SystemE

theorem helper_1_3_step5 (a d e c₀ c₁ : Point)
    (h1 : |(a─e)| = |(a─d)|) (h2 : |(c₀─c₁)| = |(a─d)|) :
    |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)| := by
  euclid_finish
