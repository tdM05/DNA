import SystemE

namespace Elements.Book2

theorem helper_2_12_step1 (a c d : Point)
    (h1 : between d a c) :
    |(d─c)| * |(d─c)| = |(c─a)| * |(c─a)| + |(a─d)| * |(a─d)| + 2 * (|(c─a)| * |(a─d)|) := by
  have hseg : |(d─c)| = |(a─d)| + |(c─a)| := by euclid_finish
  rw [hseg]; ring

end Elements.Book2
