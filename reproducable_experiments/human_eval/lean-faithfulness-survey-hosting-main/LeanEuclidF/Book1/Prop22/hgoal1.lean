import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_22_x2 (f k a a' : Point) (h11 : |(k─f)| = |(a─a')|) :
    |(f─k)| = |(a─a')| :=
  (segment_symmetric f k).trans h11

end Elements.Book1
