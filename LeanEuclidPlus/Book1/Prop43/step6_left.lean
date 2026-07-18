import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step6_left
  (a b c d e f g h k : Point) (AD BC AB CD AC EF GH : Line)
  (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
  (h_b_BC : b.onLine BC) (h_c_BC : c.onLine BC)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
  (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_dc : d ≠ c)
  (h_ab_ss_CD : a.sameSide b CD)
  (h_AD_BC : ¬AD.intersectsLine BC) (h_AB_CD : ¬AB.intersectsLine CD)
  (h_a_AC : a.onLine AC) (h_c_AC : c.onLine AC) (h_ac : a ≠ c)
  (h_k_AC : k.onLine AC)
  (h_ahd : between a h d)
  (h_e_EF : e.onLine EF) (h_k_EF : k.onLine EF)
  (h_e_AB : e.onLine AB)
  (h_h_GH : h.onLine GH) (h_k_GH : k.onLine GH) (h_hk : h ≠ k)
  (h_ae_ss_GH : a.sameSide e GH)
  (h_AD_EF : ¬AD.intersectsLine EF) (h_AB_GH : ¬AB.intersectsLine GH)
  (h_f_EF : f.onLine EF)
  (h_g_BC : g.onLine BC) (h_g_GH : g.onLine GH)
  (h_f_CD : f.onLine CD) (h_fc : f ≠ c)
  (h_kg_ss_CD : k.sameSide g CD)
  (h_EF_BC : ¬EF.intersectsLine BC) (h_GH_CD : ¬GH.intersectsLine CD)
  : Triangle.area △ a:b:c
      = Triangle.area △ a:e:k + Triangle.area △ k:e:b + Triangle.area △ b:g:k + Triangle.area △ k:g:c := by
  euclid_apply (sum_areas_if a c k b AC)
  euclid_apply (sum_areas_if a b e k AB)
  euclid_apply (sum_areas_if b c g k BC)
  euclid_finish

end Elements.Book1
