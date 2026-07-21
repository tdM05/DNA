import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step6
    (AB CD GK : Line) (a c d g k : Point)
    (hgGK : g.onLine GK) (hkGK : k.onLine GK)
    (haAB : a.onLine AB) (hgAB : g.onLine AB) (hga : g ≠ a)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hkCD : k.onLine CD)
    (hckd : between c k d) (hca : c.sameSide a GK)
    : a.opposingSides d GK := by
  -- c and a on the same side of GK; between c k d with k on GK ⟹ c and d opposite ⟹ a and d opposite
  euclid_finish

end Elements.Book1
