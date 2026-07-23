import SystemE
import Book1.Prop06.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_step19 (a b c d : Point) (AC AB DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬ b.onLine AC)
    (hbtw : between a d c) (hmid : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hstep3 : distinctPointsOnLine a b AB)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : ∠ a:b:d = ∠ b:a:d)   -- "angle $ABD$ is equal to $BAD$"
    (hassump2 : |(a─d)| = |(b─d)| ∧ |(a─d)| = |(d─c)|)   -- "$AD$ becomes equal to each of $BD$ [Prop.~1.6] and $DC$"
    : |(d─a)| = |(d─b)| ∧ |(d─b)| = |(d─c)| := by
  -- Triangle DAB is isosceles: ∠DAB = ∠DBA, so DA = DB [Prop.~1.6].
  have hda : d ≠ a := by euclid_finish
  have haoffDB : ¬ a.onLine DB := by
    intro haDB
    euclid_apply (two_points_determine_line a d AC DB)
    euclid_finish
  have hACneAB : AC ≠ AB := fun h => hboff (h ▸ hbAB)
  have hABneDB : AB ≠ DB := fun h => haoffDB (h ▸ haAB)
  have hDBneAC : DB ≠ AC := fun h => hboff (h ▸ hbDB)
  have htri : formTriangle d a b AC AB DB := by euclid_finish
  euclid_apply (proposition_6 d a b AC AB DB)
  euclid_finish

end Elements.Book3
