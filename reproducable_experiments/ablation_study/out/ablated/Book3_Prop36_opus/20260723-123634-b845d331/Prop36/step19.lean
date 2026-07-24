import SystemE

namespace Elements.Book3

-- since AC is cut in half at F, let CD be added to it.
theorem helper_3_36_step19 (a c f : Point)
    (h1 : |(a─f)| = |(f─c)|) :
    |(a─f)| = |(f─c)| := by
  euclid_finish

end Elements.Book3
