import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step19 (a b c d : Point) (AC AB DB : Line)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC) (hadc : between a d c)
    (hb_off : ¬b.onLine AC)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:b:d = ∠ b:a:d)   -- "angle $ABD$ is equal to $BAD$"
  (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)   -- "$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$"
  : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  -- triangle ABD has equal base angles ∠DAB = ∠DBA, so DA = DB [Prop.~1.6]
  euclid_apply (Elements.Book1.proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
