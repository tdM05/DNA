import SystemE

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_22_hgoal1 (f k a a' : Point) (h11 : |(k─f)| = |(a─a')|) :
    |(f─k)| = |(a─a')| :=
  (segment_symmetric f k).trans h11

end Elements.Book1
