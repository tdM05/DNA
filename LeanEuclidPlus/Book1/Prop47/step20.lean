import SystemE
import Book1.Prop47.step20_gb_par
import Book1.Prop47.step20_hc_par
import Book1.Prop47.step20_gb
import Book1.Prop47.step20_hc
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step20
    (a b c f g h k : Point) (GF AB AG BF HK AC AH CK : Line)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hgAG : g.onLine AG) (haAG : a.onLine AG)
    (hfBF : f.onLine BF) (hbBF : b.onLine BF) (hfb : f ≠ b)
    (hgaBF : g.sameSide a BF)
    (hGFAB : ¬GF.intersectsLine AB) (hAGBF : ¬AG.intersectsLine BF)
    (hhHK : h.onLine HK) (hkHK : k.onLine HK)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (hhAH : h.onLine AH) (haAH : a.onLine AH)
    (hkCK : k.onLine CK) (hcCK : c.onLine CK) (hkc : k ≠ c)
    (hhaCK : h.sameSide a CK)
    (hHKAC : ¬HK.intersectsLine AC) (hAHCK : ¬AH.intersectsLine CK)
    (hbag : ∠ b:a:g = ∟) (hcah : ∠ c:a:h = ∟)
    (hgflen : |(g─f)| = |(a─b)|) (haglen : |(a─g)| = |(a─b)|)
    (hhklen : |(h─k)| = |(a─c)|) (hahlen : |(a─h)| = |(a─c)|) :
    (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|) := by
  have step20_gb_par : formParallelogram g f a b GF AB AG BF := by euclid_apply (helper_1_47_step20_gb_par a b f g GF AB AG BF (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show g.sameSide a BF; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬AG.intersectsLine BF; assumption)))
  have step20_hc_par : formParallelogram h k a c HK AC AH CK := by euclid_apply (helper_1_47_step20_hc_par a c h k HK AC AH CK (by euclid_assumption "" (show h.onLine HK; assumption)) (by euclid_assumption "" (show k.onLine HK; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show k.onLine CK; assumption)) (by euclid_assumption "" (show c.onLine CK; assumption)) (by euclid_assumption "" (show k ≠ c; assumption)) (by euclid_assumption "" (show h.sameSide a CK; assumption)) (by euclid_assumption "" (show ¬HK.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬AH.intersectsLine CK; assumption)))
  have step20_gb : Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)| := by euclid_apply (helper_1_47_step20_gb a b f g GF AB AG BF (by euclid_assumption "" (show formParallelogram g f a b GF AB AG BF; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ∠ b:a:g = ∟; assumption)) (by euclid_assumption "" (show |(g─f)| = |(a─b)|; assumption)) (by euclid_assumption "" (show |(a─g)| = |(a─b)|; assumption)))
  have step20_hc : Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)| := by euclid_apply (helper_1_47_step20_hc a c h k HK AC AH CK (by euclid_assumption "" (show formParallelogram h k a c HK AC AH CK; assumption)) (by euclid_assumption "" (show h.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AH; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ∠ c:a:h = ∟; assumption)) (by euclid_assumption "" (show |(h─k)| = |(a─c)|; assumption)) (by euclid_assumption "" (show |(a─h)| = |(a─c)|; assumption)))
  exact ⟨step20_gb, step20_hc⟩

end Elements.Book1
