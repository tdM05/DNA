import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3
open Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_3_25_step9 (a b c d e e0p : Point) (AC AE AB DB : Line)
    (haAC : a.onLine AC) (hbAC : ¬b.onLine AC) (hadc : between a d c) (hdDB : d.onLine DB)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (heDB : e.onLine DB) (hbDB : b.onLine DB) (hab : a ≠ b)
    (he0pAE : e0p.onLine AE) (he0p_side : e0p.sameSide d AB)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ a:b:e = ∠ b:a:e)   -- "angle $ABE$ is equal to $BAE$"
    : |(e─b)| = |(e─a)| := by
  -- Isosceles △EAB: base angles ∠EAB = ∠EBA ⟹ EA = EB [Prop.~1.6].
  have hbAE : ¬ b.onLine AE := by euclid_finish
  have htri : formTriangle e a b AE AB DB := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> euclid_finish
  euclid_apply (proposition_6 e a b AE AB DB)
  euclid_finish

end Elements.Book3
