import SystemE
import Book1.Prop30.step7_othercases_opp
import Book1.Prop30.step7_othercases_c2_ang1
import Book1.Prop30.step7_othercases_c2_ang2
import Book1.Prop30.step7_othercases_c2_ang
import Book1.Prop30.step7_othercases_c2
import Book1.Prop30.step7_othercases_c3_ang1
import Book1.Prop30.step7_othercases_c3_ang2
import Book1.Prop30.step7_othercases_c3_ang
import Book1.Prop30.step7_othercases_c3
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_30_s7_x1
    (AB CD EF GK : Line) (a b c d e f g h k : Point)
    (hg_AB : g.onLine AB) (ha_AB : a.onLine AB) (hb_AB : b.onLine AB)
    (hk_CD : k.onLine CD) (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hh_EF : h.onLine EF) (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_agb : between a g b)
    (hbetw_ehf : between e h f)
    (hbetw_ckd : between c k d)
    (heside : e.sameSide a GK)
    (hcside : c.sameSide a GK)
    (hnopar_AB : ¬AB.intersectsLine EF)
    (hnopar_CD : ¬CD.intersectsLine EF)
    (hnot_ghk : ¬between g h k)
    (hgk : g ≠ k)
    (hCDneEF : CD ≠ EF)
    (hEFneAB : EF ≠ AB)
    : ¬(AB.intersectsLine CD) := by
  by_cases hc2 : between g k h
  ·
    have s7_x13 : a.opposingSides d GK := by euclid_apply (h_1_30_s7_x10 GK a c d k (by (show k.onLine GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show between c k d; assumption)))
    have s7_x7 : ∠ a:g:h = ∠ g:h:f := by euclid_apply (h_1_30_s7_x4 AB EF GK a b e f g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between e h f; assumption)) (by (show between g k h; assumption)) (by (show e.sameSide a GK; assumption)) (by (show ¬AB.intersectsLine EF; assumption)))
    have s7_x8 : ∠ g:k:d = ∠ k:h:f := by euclid_apply (h_1_30_s7_x5 EF CD GK a c d e f g h k (by (show k.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between e h f; assumption)) (by (show between c k d; assumption)) (by (show between g k h; assumption)) (by (show e.sameSide a GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show ¬CD.intersectsLine EF; assumption)))
    have s7_x6 : ∠ a:g:k = ∠ g:k:d := by euclid_apply (h_1_30_s7_x3 AB EF GK a b d e f g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between e h f; assumption)) (by (show between g k h; assumption)) (by (show e.sameSide a GK; assumption)) (by (show ¬AB.intersectsLine EF; assumption)) (by (show ∠ a:g:h = ∠ g:h:f; assumption)) (by (show ∠ g:k:d = ∠ k:h:f; assumption)))
    have s7_x5 : ¬(AB.intersectsLine CD) := by euclid_apply (h_1_30_s7_x2 AB CD GK a b c d g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show k.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show g.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between c k d; assumption)) (by (show between g k h; assumption)) (by (show ∠ a:g:k = ∠ g:k:d; assumption)) (by (show a.opposingSides d GK; assumption)))
    exact s7_x5
  ·
    have hkh : k ≠ h := by euclid_finish
    have hgh : g ≠ h := by euclid_finish
    have s7_x13 : a.opposingSides d GK := by euclid_apply (h_1_30_s7_x10 GK a c d k (by (show k.onLine GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show between c k d; assumption)))
    have s7_x11 : ∠ d:k:h = ∠ k:h:e := by euclid_apply (h_1_30_s7_x8 EF CD GK a c d e f g h k (by (show k.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between e h f; assumption)) (by (show between c k d; assumption)) (by (show e.sameSide a GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show ¬CD.intersectsLine EF; assumption)) (by (show ¬between g h k; assumption)) (by (show ¬between g k h; assumption)) (by (show k ≠ h; assumption)))
    have s7_x12 : ∠ k:g:a = ∠ g:h:e := by euclid_apply (h_1_30_s7_x9 AB EF GK a b e f g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between e h f; assumption)) (by (show e.sameSide a GK; assumption)) (by (show ¬AB.intersectsLine EF; assumption)) (by (show ¬between g h k; assumption)) (by (show ¬between g k h; assumption)) (by (show g ≠ k; assumption)) (by (show k ≠ h; assumption)) (by (show g ≠ h; assumption)))
    have s7_x10 : ∠ a:g:k = ∠ g:k:d := by euclid_apply (h_1_30_s7_x7 AB CD EF GK a b c d e f g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show k.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show h.onLine EF; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between e h f; assumption)) (by (show between c k d; assumption)) (by (show e.sameSide a GK; assumption)) (by (show c.sameSide a GK; assumption)) (by (show ¬AB.intersectsLine EF; assumption)) (by (show ¬CD.intersectsLine EF; assumption)) (by (show ¬between g h k; assumption)) (by (show ¬between g k h; assumption)) (by (show g ≠ k; assumption)) (by (show k ≠ h; assumption)) (by (show g ≠ h; assumption)) (by (show ∠ d:k:h = ∠ k:h:e; assumption)) (by (show ∠ k:g:a = ∠ g:h:e; assumption)))
    have s7_x9 : ¬(AB.intersectsLine CD) := by euclid_apply (h_1_30_s7_x6 AB CD GK a b c d g h k (by (show g.onLine AB; assumption)) (by (show a.onLine AB; assumption)) (by (show k.onLine CD; assumption)) (by (show d.onLine CD; assumption)) (by (show g.onLine GK; assumption)) (by (show h.onLine GK; assumption)) (by (show k.onLine GK; assumption)) (by (show between a g b; assumption)) (by (show between c k d; assumption)) (by (show ¬between g h k; assumption)) (by (show ¬between g k h; assumption)) (by (show g ≠ k; assumption)) (by (show ∠ a:g:k = ∠ g:k:d; assumption)) (by (show a.opposingSides d GK; assumption)))
    exact s7_x9

end Elements.Book1
