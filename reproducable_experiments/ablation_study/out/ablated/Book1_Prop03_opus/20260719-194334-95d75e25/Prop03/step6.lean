import SystemE

theorem helper_1_3_step6 (a d e c₀ c₁ : Point)
    (h1 : |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)|) :
    |(a─e)| = |(c₀─c₁)| := by
  euclid_finish
