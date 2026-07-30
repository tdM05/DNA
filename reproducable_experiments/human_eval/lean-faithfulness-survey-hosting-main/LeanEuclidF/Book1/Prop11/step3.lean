import SystemE
import Book1.Prop11.step3_foff
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_11_s3
    (a b c d e f : Point) (AB DF FE : Line)
    (hacb : between a c b)
    (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hdAB : d.onLine AB) (hdc : between c d a) (hce : between c e b)
    (hfd : |(f─d)| = |(d─e)|) (hfe : |(f─e)| = |(d─e)|)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF)
    (hfFE : f.onLine FE) (heFE : e.onLine FE) :
    formTriangle f d e DF AB FE ∧ |(f─d)| = |(d─e)| ∧ |(f─e)| = |(d─e)| := by
  have s3_x3 : ¬(f.onLine AB) := by euclid_apply (h_1_11_s3_x1 a b c d e f AB (by (show between a c b; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine AB; assumption)) (by (show between c d a; assumption)) (by (show between c e b; assumption)) (by (show |(f─d)| = |(d─e)|; assumption)) (by (show |(f─e)| = |(d─e)|; assumption)))
  refine ⟨?_, hfd, hfe⟩
  refine ⟨⟨hfDF, hdDF, ?_⟩, hdAB, ?_, heFE, hfFE, ?_, ?_, ?_⟩ <;> euclid_finish

end Elements.Book1
