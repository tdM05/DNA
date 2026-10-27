import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_bet
  (a c d f : Point) (DA : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA)
  (hbet_dca : between d c a)
  (hfDA : f.onLine DA)
  (step17_af : a ≠ f) (step17_cf : c ≠ f)
  (step17_feq : |(f─a)| = |(f─c)|)
  : between a f c := by
  euclid_finish

end Elements.Book3
