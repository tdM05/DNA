import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step6_hdab (a d d' : Point) (AB : Line)
    (haAB : a.onLine AB) (hd'AB : d'.onLine AB) (hadd' : between a d d')
    : d.onLine AB := by
  euclid_apply (between_same_line_in a d d' AB)
  euclid_finish

end Elements.Book1
