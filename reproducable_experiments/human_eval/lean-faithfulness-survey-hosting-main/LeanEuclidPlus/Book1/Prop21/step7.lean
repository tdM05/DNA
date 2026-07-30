import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_21_s7 (a b c e : Point)
    (hstep4 : |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)|) :
    |(b─a)| + |(a─c)| > |(b─e)| + |(e─c)| := hstep4

end Elements.Book1
