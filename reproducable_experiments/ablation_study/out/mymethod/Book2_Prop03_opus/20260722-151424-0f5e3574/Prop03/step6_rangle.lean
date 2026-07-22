import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

theorem helper_2_3_step6_rangle (a b c d e f : Point) (CD DE : Line)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hd_DE : d.onLine DE)
    (he_DE : e.onLine DE) (hf_DE : f.onLine DE)
    (hacb : between a c b) (hcde : ∠ c:d:e = ∟) (hedf : between e d f)
    (hcd_eq : |(c─d)| = |(c─b)|) :
    ∠ c:d:f = ∟ := by
  have hcd_ne : c ≠ d := by euclid_finish
  have hc_notDE : ¬(c.onLine DE) := by
    intro hcDE
    euclid_apply (two_points_determine_line c d DE CD)
    euclid_finish
  euclid_apply (perpendicular_onlyif e f d c DE)
  euclid_finish

end Elements.Book2
