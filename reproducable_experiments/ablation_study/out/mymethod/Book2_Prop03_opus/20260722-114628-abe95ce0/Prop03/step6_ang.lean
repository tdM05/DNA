import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6_ang (c d e f : Point) (DE : Line)
    (hd_de : d.onLine DE) (he_de : e.onLine DE) (hf_de : f.onLine DE)
    (hcd : c ≠ d)
    (hang_cde : ∠ c:d:e = ∟) (hbet2 : between e d f) :
    ∠ c:d:f = ∟ := by
  have hde : d ≠ e := by euclid_finish
  have hdc : d ≠ c := hcd.symm
  have hedc : ∠ e:d:c = ∟ := by euclid_finish
  have hc_nde : ¬c.onLine DE := offLine_of_right_angle d e c DE hd_de he_de hde hdc hedc
  euclid_apply (perpendicular_onlyif e f d c DE)
  euclid_finish

end Elements.Book2
