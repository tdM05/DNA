import SystemE
import Book1.Prop13.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step7_othercases_angK (AB CD GK : Line) (a c d f g h k : Point)
  (hg_ab : g.onLine AB) (ha_ab : a.onLine AB) (hga_ne : g ≠ a)
  (hk_cd : k.onLine CD) (hc_cd : c.onLine CD) (hd_cd : d.onLine CD) (hckd : between c k d)
  (hg_gk : g.onLine GK) (hh_gk : h.onLine GK) (hk_gk : k.onLine GK) (hgk_ne : g ≠ k)
  (hkh_ne : k ≠ h) (hgh_ne : g ≠ h) (hab_gk : AB ≠ GK) (hcd_gk : CD ≠ GK)
  (ha_off : ¬a.onLine GK)
  (hang1 : ∠ a:g:h = ∠ g:h:f) (hang2 : ∠ c:k:h = ∠ k:h:f) (hhf : ∠ g:h:f = ∠ k:h:f) :
  between g k h → ∠ a:g:k = ∠ g:k:d := by
  intro hord
  have hac : ∠ a:g:h = ∠ c:k:h := by rw [hang1, hhf, ← hang2]
  -- linear pair at k on the straight line c-k-d with ray k→g:  ∠c:k:g + ∠g:k:d = 2∟
  euclid_apply (proposition_13 g k c d GK CD)
  -- linear pair at k on the straight line g-k-h with ray k→c:  ∠g:k:c + ∠c:k:h = 2∟
  euclid_apply (proposition_13 c k g h CD GK)
  -- hence ∠g:k:d = ∠c:k:h = ∠a:g:h = ∠a:g:k (rays g→k = g→h since k is the middle crossing)
  euclid_finish

end Elements.Book1
