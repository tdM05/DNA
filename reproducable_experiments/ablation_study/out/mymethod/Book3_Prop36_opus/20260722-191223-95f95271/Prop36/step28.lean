import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step28
  (b d e : Point) (ABC : Circle) (EB ED DB : Line)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB)
  (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (hb_circ : b.onCircle ABC) (hecenter : e.isCentre ABC)
  (hnint : ¬ DB.intersectsCircle ABC)
  (hd_in : ¬ d.insideCircle ABC) (hd_on : ¬ d.onCircle ABC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ e:b:d = ∟)   -- "$EBD$ (is) a right-angle"
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  have hd_notEB : ¬ d.onLine EB := by
    intro hdEB
    euclid_apply (between_points e b d EB)
    euclid_finish
  have hne : EB ≠ ED := by
    intro heq
    rw [heq] at hd_notEB
    euclid_finish
  euclid_apply (Elements.Book1.proposition_47 b e d EB ED DB)
  euclid_finish

end Elements.Book3
