import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

theorem helper_3_25_step18 (a b c d : Point) (AC AB DB : Line)
  (haAC : a.onLine AC) (hcAC : c.onLine AC) (hbAC : ¬b.onLine AC) (hadc : between a d c)
  (hdDB : d.onLine DB) (hbDB : b.onLine DB) (haAB : a.onLine AB) (hbAB : b.onLine AB)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : ∠ a:b:d = ∠ b:a:d)   -- "angle $ABD$ is equal to $BAD$"
  (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)   -- "$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$"
  : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  -- Isosceles △DAB: base angles ∠DAB = ∠DBA ⟹ DA = DB [Prop.~1.6]; DA = DC from the bisection.
  have htri : formTriangle d a b AC AB DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
