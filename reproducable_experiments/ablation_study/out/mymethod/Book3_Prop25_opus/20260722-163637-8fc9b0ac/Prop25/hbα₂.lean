import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hbα₂ (a b c d : Point) (α₂ : Circle)
    (hd_centre : d.isCentre α₂) (ha_circle : a.onCircle α₂)
    (hda_db : |(d─a)| = |(d─b)|) (hdb_dc : |(d─b)| = |(d─c)|) :
    b.onCircle α₂ := by
  euclid_finish

end Elements.Book3
