import SystemE
import Book1.Prop31.Main
import Book1Variants.Prop46

namespace Elements.Book1

theorem prop47_pre1 : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  have hoffBD : ¬(a.onLine BD) := by sorry
  euclid_apply (proposition_31 a b d BD) as AL
  have hALBC : AL.intersectsLine BC := by euclid_finish
  sorry

end Elements.Book1
