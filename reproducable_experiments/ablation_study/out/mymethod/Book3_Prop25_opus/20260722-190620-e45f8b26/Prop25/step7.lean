import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step7 (e : Point) (DB : Line) (heDB : e.onLine DB) :
    e.onLine DB := heDB

end Elements.Book3
