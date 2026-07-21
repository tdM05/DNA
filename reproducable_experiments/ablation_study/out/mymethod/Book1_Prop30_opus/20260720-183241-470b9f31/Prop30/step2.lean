import SystemE
import Book1.Prop29.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step2 (AB EF GK : Line) (a b g h k e f : Point)
  (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (hk_gk : k.onLine GK)
  (ha_ab : a.onLine AB) (hb_ab : b.onLine AB) (hagb : between a g b)
  (he_ef : e.onLine EF) (hea_ss : e.sameSide a GK)
  (hf_ef : f.onLine EF) (hehf : between e h f)
  (hghk : between g h k)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AB.intersectsLine GK ∧ EF.intersectsLine GK ∧ ¬(AB.intersectsLine EF))   -- "the straight-line $GK$ has fallen across the parallel straight-lines $AB$ and $EF$"
  : ∠ a:g:k = ∠ g:h:f := by
  have hab_ef : ¬(AB.intersectsLine EF) := hassump1.2.2
  -- construct x on GK, before g (between h g x, i.e. x g h order)
  have hhg_ne : h ≠ g := by
    intro heq
    euclid_apply (intersection_lines_common_point g AB EF)
    euclid_finish
  euclid_apply (extend_point GK h g) as x
  -- b and f lie on the same side of GK (a↔e same side; a,b opposite; e,f opposite)
  have hbf : b.sameSide f GK := by euclid_finish
  -- proposition 1.29 on parallels AB, EF with transversal GK
  euclid_apply (proposition_29 a b e f x k g h AB EF GK)
  euclid_finish

end Elements.Book1
