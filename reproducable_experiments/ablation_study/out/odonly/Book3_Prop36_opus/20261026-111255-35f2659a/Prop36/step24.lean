import SystemE
import Book1.Prop47.Main
import Book3.Prop36.step24_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24 (a c d e f : Point) (DA EF ED : Line)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (hdca : between d c a)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (henef : e ≠ f) (hhalf : |(a─f)| = |(f─c)|)
  (hperpall : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟) :
    |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hdnef : d ≠ f := by euclid_finish
  have hdfe : ∠ d:f:e = ∟ := hperpall d hdDA hdnef
  have heoff : ¬ e.onLine DA := by euclid_finish
  have step24_tri : formTriangle f d e DA ED EF := by euclid_apply (helper_3_36_step24_tri d e f DA EF ED (by euclid_assumption "" (show f.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show e ≠ f; assumption)) (by euclid_assumption "" (show d ≠ f; assumption)) (by euclid_assumption "" (show ¬ e.onLine DA; assumption)))
  euclid_apply (Elements.Book1.proposition_47 f d e DA ED EF ⟨step24_tri, hdfe⟩)
  euclid_finish

end Elements.Book3
