import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2
    (AB CD EF GK : Line) (a b e f g h k : Point)
    (hgAB : g.onLine AB) (haAB : a.onLine AB) (hga : g ≠ a) (hbAB : b.onLine AB)
    (hagb : between a g b)
    (hgGK : g.onLine GK) (hhGK : h.onLine GK) (hkGK : k.onLine GK)
    (hhEF : h.onLine EF) (heEF : e.onLine EF) (hfEF : f.onLine EF)
    (hehf : between e h f) (hea : e.sameSide a GK)
    (hghk : between g h k)
    (hABEF : ¬AB.intersectsLine EF)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$"
    : ∠ a:g:k = ∠ g:h:f := by
  -- construct a point p on GK on the far side of g from h: between h g p (= between p g h)
  euclid_apply (extend_point GK h g) as p
  -- b and f lie on the same side of GK (both opposite a): needed for prop29's sameSide precondition
  have hbf : b.sameSide f GK := by euclid_finish
  euclid_apply (proposition_29 a b e f p k g h AB EF GK)
  -- prop29 gives ∠ a:g:h = ∠ g:h:f; since between g h k, ray g→h = ray g→k
  euclid_finish

end Elements.Book1
