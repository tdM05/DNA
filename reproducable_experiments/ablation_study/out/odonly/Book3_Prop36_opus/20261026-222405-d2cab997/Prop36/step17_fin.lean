import SystemE
import Book1.Prop47.Main
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step17_fin (a e f : Point) (ABC : Circle) (DA EF : Line)
    (hada : a.onLine DA) (hfDA : f.onLine DA) (hfEF : f.onLine EF) (heEF : e.onLine EF)
    (hacirc : a.onCircle ABC) (hecentre : e.isCentre ABC) (hennotDA : ¬ e.onLine DA)
    (haf : a ≠ f) (hra : ∠ a:f:e = ∟) :
    f.insideCircle ABC := by
  euclid_apply (line_from_points e a) as EA
  euclid_apply (proposition_47 f e a EF EA DA)
  have hlt : |(e─f)| < |(e─a)| := by euclid_finish
  euclid_finish

end Elements.Book3
