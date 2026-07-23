import SystemE

namespace Elements.Book2

-- So the square on $CB$ is greater than the (sum of the) squares on $CA$ and $AB$ by twice the
-- rectangle contained by $CA$ and $AD$. (Restates step 6 using segment symmetry.)
theorem helper_2_12_step7 (a b c d : Point)
    (h1 : |(c─b)| * |(c─b)| = |(c─a)| * |(c─a)| + |(a─b)| * |(a─b)| + 2 * (|(c─a)| * |(a─d)|)) :
    |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| + 2 * (|(c─a)| * |(a─d)|) := by
  euclid_finish

end Elements.Book2
