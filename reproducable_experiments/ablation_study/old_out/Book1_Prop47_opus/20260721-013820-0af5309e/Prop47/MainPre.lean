import SystemE
import Book1.Prop31.Main
import Book1Variants.Prop46
import Book1.Prop47.bmc
import Book1.Prop47.amperp
import Book1.Prop47.alce
import Book1.Prop47.dle

namespace Elements.Book1

theorem prop47_pre : ∀ (a b c: Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ b:a:c : ℝ) = ∟ →
  |(b─c)| * |(b─c)| = |(b─a)| * |(b─a)| + |(a─c)| * |(a─c)| := by
  euclid_intros
  euclid_apply (proposition_46' b c a BC) as (d, e, DE, BD, CE)
  euclid_apply (proposition_46' a b c AB) as (g, f, GF, AG, BF)
  euclid_apply (proposition_46' a c b AC) as (h, k, HK, AH, CK)
  have hoffBD : ¬(a.onLine BD) := by euclid_finish
  euclid_apply (proposition_31 a b d BD) as AL
  have hALDE : AL.intersectsLine DE := by euclid_finish
  euclid_apply (intersection_lines AL DE) as l
  have hALBC : AL.intersectsLine BC := by euclid_finish
  euclid_apply (intersection_lines AL BC) as m
  euclid_apply (helper_1_47_bmc a b c d m AB BC AC BD AL)
  sorry

end Elements.Book1
