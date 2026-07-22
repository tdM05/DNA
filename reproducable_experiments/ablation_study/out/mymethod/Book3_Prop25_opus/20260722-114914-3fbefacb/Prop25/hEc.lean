import SystemE
import Book1.Prop04.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_25_hEc (a b c d e : Point) (AC DB AG3 : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c) (haddc : |(a─d)| = |(d─c)|)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (hadbperp : ∠ a:d:b = ∟)
    (haAG3 : a.onLine AG3) (heAG3 : e.onLine AG3)
    (step22 : e.onLine DB ∧ e.sameSide b AC) :
    |(e─a)| = |(e─c)| := by
  obtain ⟨_, hesb⟩ := step22
  euclid_apply (line_from_points c e) as EC
  -- both base angles at d are right (perpendicular DB, a-d-c collinear)
  have hde : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟ := by euclid_finish
  have htri1 : formTriangle d a e AC AG3 DB := by euclid_finish
  have htri2 : formTriangle d c e AC EC DB := by euclid_finish
  -- SAS: △dae ≅ △dce (da=dc, de common, ∠adе=∠cde), so ae=ce  [Prop.~1.4]
  euclid_apply (proposition_4 d a e d c e AC AG3 DB AC EC DB)
  euclid_finish

end Elements.Book3
