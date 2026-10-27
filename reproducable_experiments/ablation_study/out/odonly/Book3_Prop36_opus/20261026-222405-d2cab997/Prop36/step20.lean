import SystemE
import Book2.Prop06.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step20 (a c f d : Point) (DA : Line)
    (hada : a.onLine DA) (hdda : d.onLine DA) (hfda : f.onLine DA)
    (hbdca : between d c a) (hhalf : |(a─f)| = |(f─c)|) :
    |(d─a)| * |(d─c)| + |(f─c)| * |(f─c)| = |(f─d)| * |(f─d)| := by
  euclid_apply (Elements.Book2.proposition_6 a c f d DA)
  euclid_finish

end Elements.Book3
