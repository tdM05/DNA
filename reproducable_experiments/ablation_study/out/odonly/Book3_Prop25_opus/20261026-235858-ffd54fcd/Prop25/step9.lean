import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step9 (a b c d e : Point) (AC DB AB AG : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hb_off : ¬b.onLine AC) (hadc : between a d c)
    (hd_DB : d.onLine DB) (hb_DB : b.onLine DB)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AG : a.onLine AG) (he_AG : e.onLine AG) (he_DB : e.onLine DB)
    (hstep6 : ∠ b:a:e = ∠ a:b:d ∧ e ≠ a)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:b:e = ∠ b:a:e)   -- "angle $ABE$ is equal to $BAE$"
  : |(e─b)| = |(e─a)| := by
  obtain ⟨hstep6a, hea⟩ := hstep6
  -- triangle EAB has equal base angles ∠EAB = ∠EBA, so EA = EB [Prop.~1.6]
  euclid_apply (Elements.Book1.proposition_6 e a b AG AB DB)
  euclid_finish

end Elements.Book3
