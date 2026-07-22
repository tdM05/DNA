import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements

theorem helper_3_25_step12_tri1 (a b c d e : Point) (AC AG DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (haAG : a.onLine AG) (heAG : e.onLine AG)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (hadbperp : ∠ a:d:b = ∟)
    (hperp2 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    (hbae : ∠ b:a:e = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d) :
    formTriangle d a e AC AG DB := by
  obtain ⟨hade, hcde⟩ := hperp2
  have hda : d ≠ a := by euclid_finish
  have hdb : d ≠ b := by euclid_finish
  have hde : d ≠ e := by intro h; subst h; euclid_finish
  have hdAC : d.onLine AC := by euclid_finish
  have heoffAC : ¬ e.onLine AC := offLine_of_right_angle d a e AC hdAC haAC hda hde hade
  have haoffDB : ¬ a.onLine DB :=
    offLine_of_right_angle d b a DB hdDB hbDB hdb hda (by euclid_finish)
  euclid_finish

end Elements.Book3
