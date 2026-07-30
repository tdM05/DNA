import SystemE
import Book1.Prop08.Main
import Book1.Prop11.step8_tri1
import Book1.Prop11.step8_tri2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s8
    (a b c d e f : Point) (AB DF FE FC : Line)
    (hacb : between a c b) (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hfFC : f.onLine FC) (hcFC : c.onLine FC)
    (hDFneAB : DF ≠ AB) (hABneFE : AB ≠ FE) (hFEneDF : FE ≠ DF)
    (hcd_eq_ce : |(c─d)| = |(c─e)|) (hdf_eq_fe : |(d─f)| = |(f─e)|) :
    ∠ d:c:f = ∠ e:c:f := by
  have s8_x12 : formTriangle c d f AB DF FC := by euclid_apply (h_1_11_s8_x1 a b c d e f AB DF FC (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show d.onLine DF; assumption)) (by (show f.onLine DF; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show DF ≠ AB; assumption)))
  have s8_x13 : formTriangle c e f AB FE FC := by euclid_apply (h_1_11_s8_x2 a b c d e f AB FE FC (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)) (by (show f.onLine FE; assumption)) (by (show e.onLine FE; assumption)) (by (show f.onLine FC; assumption)) (by (show c.onLine FC; assumption)) (by (show AB ≠ FE; assumption)))
  euclid_apply (proposition_8 c d f c e f AB DF FC AB FE FC)
  euclid_finish
