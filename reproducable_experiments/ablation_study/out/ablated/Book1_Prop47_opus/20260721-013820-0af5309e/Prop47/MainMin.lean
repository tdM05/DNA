import SystemE
import Book1Variants.Prop46
import Book1.Prop47.step1

namespace Elements.Book1

theorem prop47_min : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  have step1test :=
    helper_1_47_step1 a b c d e f g h k
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
      (by assumption)
  sorry

end Elements.Book1
