import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements

theorem helper_3_25_step12_tri2 (a b c d e : Point) (AC EC DB : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hboff : ¬b.onLine AC)
    (hadc : between a d c)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB) (heDB : e.onLine DB)
    (hadbperp : ∠ a:d:b = ∟)
    (hperp2 : ∠ a:d:e = ∟ ∧ ∠ c:d:e = ∟)
    (hbae : ∠ b:a:e = ∠ a:b:d) (hgt : ∠ a:b:d > ∠ b:a:d) :
    formTriangle d c e AC EC DB := by
  obtain ⟨hade, hcde⟩ := hperp2
  have hdc : d ≠ c := by euclid_finish
  have hde : d ≠ e := by intro h; subst h; euclid_finish
  have hdAC : d.onLine AC := by euclid_finish
  have heoffAC : ¬ e.onLine AC := offLine_of_right_angle d c e AC hdAC hcAC hdc hde hcde
  have hcoffDB : ¬ c.onLine DB := by
    intro hcDB
    euclid_apply (two_points_determine_line c d DB AC)
    euclid_finish
  euclid_finish

end Elements.Book3
