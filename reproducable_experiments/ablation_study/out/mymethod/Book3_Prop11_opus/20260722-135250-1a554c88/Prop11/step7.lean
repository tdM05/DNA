import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step7 (g d h : Point)
    (hd_bet_gdh : between g d h)
    (step6 : |(g─d)| > |(g─h)|) :
    False := by
  euclid_finish

end Elements.Book3
