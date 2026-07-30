import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_39_s5_x3
    (a e b c d : Point) (BD BC EC AE CD : Line)
    (heBD : e.onLine BD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hBDBC : BD ≠ BC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hCDBD : CD ≠ BD) (hdbne : d ≠ b)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hassump1 : ¬(AE.intersectsLine BC))
    (hasdBC : a.sameSide d BC) :
    formTriangle e b c BD BC EC := by

  have hAEneBC : AE ≠ BC :=
    fun h => (same_side_not_on_line a d BC hasdBC) (h ▸ haAE)

  have hbcne : b ≠ c := by
    intro hbc; subst hbc
    exact hCDBD (by euclid_finish)

  have hbene : e ≠ b := by
    intro heb
    have heBC : e.onLine BC := heb ▸ hbBC
    exact hassump1 (by euclid_apply (intersection_lines_common_point e AE BC); euclid_finish)

  have hBCEC : BC ≠ EC := by
    intro h
    have heBC : e.onLine BC := h.symm ▸ heEC
    exact hassump1 (by euclid_apply (intersection_lines_common_point e AE BC); euclid_finish)

  have hECBD : EC ≠ BD := by
    intro h
    have hcBD : c.onLine BD := h.symm ▸ hcEC
    exact hBDBC (by euclid_finish)
  exact ⟨⟨heBD, hbBD, hbene⟩, hbBC, hcBC, hcEC, heEC, hBDBC, hBCEC, hECBD⟩

end Elements.Book1
