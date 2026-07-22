import SystemE
import Helpers.OffLine
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6_fnotab (a b c d f : Point) (AB CD DE : Line)
    (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hd_CD : d.onLine CD) (hc_CD : c.onLine CD)
    (hd_DE : d.onLine DE) (hf_DE : f.onLine DE)
    (hacb : between a c b) (hbcd : ∠ b:c:d = ∟)
    (hDEAB : ¬(DE.intersectsLine AB)) (hcd_eq : |(c─d)| = |(c─b)|) :
    ¬(f.onLine AB) := by
  have hcb_ne : c ≠ b := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  have hd_notAB : ¬(d.onLine AB) :=
    offLine_of_right_angle c b d AB hc_AB hb_AB hcb_ne hcd_ne hbcd
  have hDE_ne_AB : DE ≠ AB := line_ne_of_offLine d DE AB hd_DE hd_notAB
  exact offLine_of_parallel_simple f DE AB hf_DE hDE_ne_AB hDEAB

end Elements.Book2
