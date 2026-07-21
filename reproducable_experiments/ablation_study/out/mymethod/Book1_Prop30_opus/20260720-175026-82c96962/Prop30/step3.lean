import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step3
    (AB CD EF GK : Line) (a c d e f g h k : Point)
    (hgGK : g.onLine GK) (hhGK : h.onLine GK) (hkGK : k.onLine GK)
    (hhEF : h.onLine EF) (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hehf : between e h f) (hea : e.sameSide a GK)
    (hkCD : k.onLine CD) (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hckd : between c k d) (hca : c.sameSide a GK)
    (hghk : between g h k)
    (hCDEF : ¬CD.intersectsLine EF)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $EF$ and $CD$"
    : ∠ g:h:f = ∠ g:k:d := by
  -- construct a point q on GK beyond k: between h k q
  euclid_apply (extend_point GK h k) as q
  -- f and d lie on the same side of GK (both opposite e ≡ opposite a): prop29's sameSide precondition
  have hfd : f.sameSide d GK := by euclid_finish
  -- prop29 on EF ∥ CD cut by GK; corresponding-angle conclusion ∠ E:G:B = ∠ G:H:D gives ∠ g:h:f = ∠ h:k:d
  euclid_apply (proposition_29 e f c d g q h k EF CD GK)
  -- since between g h k, ray k→h = ray k→g, so ∠ h:k:d = ∠ g:k:d
  euclid_finish

end Elements.Book1
