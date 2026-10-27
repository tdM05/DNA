import SystemE
import Book1.Prop47.Main
import Book3.Prop36.step28_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28 (b d e : Point) (ABC : Circle) (DB ED EB : Line)
  (heEB : e.onLine EB) (hbEB : b.onLine EB)
  (heED : e.onLine ED) (hdED : d.onLine ED)
  (hbDB : b.onLine DB) (hdDB : d.onLine DB)
  (he : e.isCentre ABC) (hbC : b.onCircle ABC)
  (hdin : ¬d.insideCircle ABC) (hdnc : ¬d.onCircle ABC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:b:d = ∟)   -- "$EBD$ (is) a right-angle"
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  have step28_tri : formTriangle b e d EB ED DB := by euclid_apply (helper_3_36_step28_tri b d e ABC DB ED EB (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show ∠ e:b:d = ∟; assumption)))
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED DB ⟨step28_tri, hassump1⟩)
  euclid_finish

end Elements.Book3
