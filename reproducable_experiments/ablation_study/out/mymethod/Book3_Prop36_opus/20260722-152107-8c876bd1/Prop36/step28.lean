import SystemE
import Book3.Prop36.step28_tri
import Book3.Prop36.step28_pyth
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28 (b d e : Point) (ABC : Circle) (EB ED DB : Line)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB)
  (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (he_centre : e.isCentre ABC) (hb_circ : b.onCircle ABC)
  (hd_notinside : ¬ d.insideCircle ABC) (hd_noncircle : ¬ d.onCircle ABC)
  (htangent : ¬ DB.intersectsCircle ABC)
  -- Reasoning hypothesis (from @assumption — keep this type in the signature):
  (hangle : ∠ e:b:d = ∟)   -- "$EBD$ (is) a right-angle"
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  have step28_tri : formTriangle b e d EB ED DB := by euclid_apply (helper_3_36_step28_tri b d e ABC EB ED DB (by euclid_assumption "" (show e.onLine EB; assumption)) (by euclid_assumption "" (show b.onLine EB; assumption)) (by euclid_assumption "" (show e.onLine ED; assumption)) (by euclid_assumption "" (show d.onLine ED; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show e.isCentre ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬ d.insideCircle ABC; assumption)) (by euclid_assumption "" (show ¬ d.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬ DB.intersectsCircle ABC; assumption)))
  have step28_pyth : |(e─d)| * |(e─d)| = |(e─b)| * |(e─b)| + |(b─d)| * |(b─d)| := by euclid_apply (helper_3_36_step28_pyth b d e EB ED DB (by euclid_assumption "" (show formTriangle b e d EB ED DB; assumption)) (by euclid_assumption "" (show ∠ e:b:d = ∟; assumption)))
  rw [segment_symmetric d b]
  rw [step28_pyth]

end Elements.Book3
