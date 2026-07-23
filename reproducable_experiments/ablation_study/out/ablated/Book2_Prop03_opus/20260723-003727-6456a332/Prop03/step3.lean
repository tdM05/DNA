import SystemE

namespace Elements.Book2

-- `AF` is drawn through `A`, parallel to `CD`: these are exactly the defining facts of the
-- line `AF` constructed by Prop.~1.31.
theorem helper_2_3_step3 (a : Point) (AF CD : Line)
    (h1 : a.onLine AF) (h2 : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) := by
  euclid_finish

end Elements.Book2
