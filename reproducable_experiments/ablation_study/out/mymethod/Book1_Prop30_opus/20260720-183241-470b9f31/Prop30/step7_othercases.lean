import SystemE
import Book1.Prop27.Main
import Book1.Prop30.step7_othercases_ghne
import Book1.Prop30.step7_othercases_hkne
import Book1.Prop30.step7_othercases_abgk
import Book1.Prop30.step7_othercases_cdgk
import Book1.Prop30.step7_othercases_efgk
import Book1.Prop30.step7_othercases_aoff
import Book1.Prop30.step7_othercases_coff
import Book1.Prop30.step7_othercases_doff
import Book1.Prop30.step7_othercases_foff
import Book1.Prop30.step7_othercases_ang1
import Book1.Prop30.step7_othercases_ang2
import Book1.Prop30.step7_othercases_hhf
import Book1.Prop30.step7_othercases_opp
import Book1.Prop30.step7_othercases_cases
import Book1.Prop30.step7_othercases_angG
import Book1.Prop30.step7_othercases_angK
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases (AB CD EF GK : Line) (a b c d e f g h k : Point)
  (hg_ab : g.onLine AB) (hg_gk : g.onLine GK)
  (hk_cd : k.onLine CD) (hk_gk : k.onLine GK) (hgk_ne : g ≠ k)
  (hh_ef : h.onLine EF) (hh_gk : h.onLine GK)
  (ha_ab : a.onLine AB) (hga_ne : g ≠ a) (hb_ab : b.onLine AB) (hagb : between a g b)
  (he_ef : e.onLine EF) (hea_ss : e.sameSide a GK) (hf_ef : f.onLine EF) (hehf : between e h f)
  (hc_cd : c.onLine CD) (hca_ss : c.sameSide a GK) (hd_cd : d.onLine CD) (hckd : between c k d)
  (hab_ef : ¬AB.intersectsLine EF) (hcd_ef : ¬CD.intersectsLine EF)
  (hne_ef_ab : EF ≠ AB) (hne_cd_ef : CD ≠ EF)
  (hnbtw : ¬between g h k) :
  ¬(AB.intersectsLine CD) := by
  -- point/line distinctness (small leaves)
  have step7_othercases_ghne : g ≠ h := by euclid_apply (helper_1_30_step7_othercases_ghne AB EF g h (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine EF; assumption)) (by euclid_assumption "" (show EF ≠ AB; assumption)))
  have step7_othercases_hkne : k ≠ h := by euclid_apply (helper_1_30_step7_othercases_hkne CD EF k h (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine EF; assumption)) (by euclid_assumption "" (show CD ≠ EF; assumption)))
  have step7_othercases_abgk : AB ≠ GK := by euclid_apply (helper_1_30_step7_othercases_abgk AB EF GK h (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine EF; assumption)) (by euclid_assumption "" (show EF ≠ AB; assumption)))
  have step7_othercases_cdgk : CD ≠ GK := by euclid_apply (helper_1_30_step7_othercases_cdgk CD EF GK h (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine EF; assumption)) (by euclid_assumption "" (show CD ≠ EF; assumption)))
  have step7_othercases_efgk : EF ≠ GK := by euclid_apply (helper_1_30_step7_othercases_efgk AB EF GK g (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine EF; assumption)) (by euclid_assumption "" (show EF ≠ AB; assumption)))
  -- off-line facts
  have step7_othercases_aoff : ¬a.onLine GK := by euclid_apply (helper_1_30_step7_othercases_aoff AB GK a g (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show AB ≠ GK; assumption)))
  have step7_othercases_coff : ¬c.onLine GK := by euclid_apply (helper_1_30_step7_othercases_coff CD GK c d k (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show between c k d; assumption)) (by euclid_assumption "" (show CD ≠ GK; assumption)))
  have step7_othercases_doff : ¬d.onLine GK := by euclid_apply (helper_1_30_step7_othercases_doff CD GK c d k (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show between c k d; assumption)) (by euclid_assumption "" (show CD ≠ GK; assumption)))
  have step7_othercases_foff : ¬f.onLine GK := by euclid_apply (helper_1_30_step7_othercases_foff EF GK e f h (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show between e h f; assumption)) (by euclid_assumption "" (show EF ≠ GK; assumption)))
  -- alternate/corresponding angle facts through EF (prop 1.29, twice)
  have step7_othercases_ang1 : ∠ a:g:h = ∠ g:h:f := by euclid_apply (helper_1_30_step7_othercases_ang1 AB EF GK a b e f g h (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between a g b; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e h f; assumption)) (by euclid_assumption "" (show e.sameSide a GK; assumption)) (by euclid_assumption "" (show ¬AB.intersectsLine EF; assumption)) (by euclid_assumption "" (show EF ≠ AB; assumption)))
  have step7_othercases_ang2 : ∠ c:k:h = ∠ k:h:f := by euclid_apply (helper_1_30_step7_othercases_ang2 CD EF GK a c d e f h k (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show between c k d; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show between e h f; assumption)) (by euclid_assumption "" (show c.sameSide a GK; assumption)) (by euclid_assumption "" (show e.sameSide a GK; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine EF; assumption)) (by euclid_assumption "" (show CD ≠ EF; assumption)))
  -- rays h→g and h→k coincide (g,k on the same side of h): ∠g:h:f = ∠k:h:f
  have step7_othercases_hhf : ∠ g:h:f = ∠ k:h:f := by euclid_apply (helper_1_30_step7_othercases_hhf EF GK f g h k (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine EF; assumption)) (by euclid_assumption "" (show f.onLine EF; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)) (by euclid_assumption "" (show g ≠ k; assumption)) (by euclid_assumption "" (show ¬between g h k; assumption)) (by euclid_assumption "" (show ¬f.onLine GK; assumption)))
  -- a and d on opposite sides of GK
  have step7_othercases_opp : a.opposingSides d GK := by euclid_apply (helper_1_30_step7_othercases_opp GK a c d k (by euclid_assumption "" (show c.sameSide a GK; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show between c k d; assumption)))
  -- g,h,k are collinear on GK and h is not between g,k: g or k is the middle crossing
  have step7_othercases_cases : between h g k ∨ between g k h := by euclid_apply (helper_1_30_step7_othercases_cases GK g h k (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)) (by euclid_assumption "" (show g ≠ k; assumption)) (by euclid_assumption "" (show ¬between g h k; assumption)))
  -- the alternate-angle equality, one lemma per ordering
  have step7_othercases_angG : between h g k → ∠ a:g:k = ∠ g:k:d := by euclid_apply (helper_1_30_step7_othercases_angG AB CD GK a c d f g h k (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show between c k d; assumption)) (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show g ≠ k; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)) (by euclid_assumption "" (show AB ≠ GK; assumption)) (by euclid_assumption "" (show CD ≠ GK; assumption)) (by euclid_assumption "" (show ¬c.onLine GK; assumption)) (by euclid_assumption "" (show ∠ a:g:h = ∠ g:h:f; assumption)) (by euclid_assumption "" (show ∠ c:k:h = ∠ k:h:f; assumption)) (by euclid_assumption "" (show ∠ g:h:f = ∠ k:h:f; assumption)))
  have step7_othercases_angK : between g k h → ∠ a:g:k = ∠ g:k:d := by euclid_apply (helper_1_30_step7_othercases_angK AB CD GK a c d f g h k (by euclid_assumption "" (show g.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show g ≠ a; assumption)) (by euclid_assumption "" (show k.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show between c k d; assumption)) (by euclid_assumption "" (show g.onLine GK; assumption)) (by euclid_assumption "" (show h.onLine GK; assumption)) (by euclid_assumption "" (show k.onLine GK; assumption)) (by euclid_assumption "" (show g ≠ k; assumption)) (by euclid_assumption "" (show k ≠ h; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show AB ≠ GK; assumption)) (by euclid_assumption "" (show CD ≠ GK; assumption)) (by euclid_assumption "" (show ¬a.onLine GK; assumption)) (by euclid_assumption "" (show ∠ a:g:h = ∠ g:h:f; assumption)) (by euclid_assumption "" (show ∠ c:k:h = ∠ k:h:f; assumption)) (by euclid_assumption "" (show ∠ g:h:f = ∠ k:h:f; assumption)))
  -- combine the two cases
  have hfinal : ∠ a:g:k = ∠ g:k:d := by
    rcases step7_othercases_cases with hord | hord
    · exact step7_othercases_angG hord
    · exact step7_othercases_angK hord
  euclid_apply (proposition_27 a d g k AB CD GK)
  euclid_finish

end Elements.Book1
