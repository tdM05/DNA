import SystemE

namespace Elements.Book1

theorem helper_1_3_step6 (a c₀ c₁ e d : Point)
  (h1 : |(a─e)| = |(a─d)| ∧ |(c₀─c₁)| = |(a─d)|) :
  |(a─e)| = |(c₀─c₁)| := by
  euclid_finish

end Elements.Book1
