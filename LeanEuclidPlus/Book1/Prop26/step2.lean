import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_26_step2 (a b c d e g : Point) (GC : Line)
    (h_bga : between b g a) (h_bg : |(b─g)| = |(e─d)|)
    (h_g_GC : g.onLine GC) (h_c_GC : c.onLine GC) :
    between b g a ∧ |(b─g)| = |(d─e)| ∧ g.onLine GC ∧ c.onLine GC := by
  euclid_finish

end Elements.Book1
