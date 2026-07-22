import SystemE
import Book1.Prop04.Main
import Book1.Prop14.Main
import Book1.Prop31.Main
import Book1.Prop41.Main
import Book1Variants.Prop46

set_option systemE.solverTime 120

namespace Elements.Book1

theorem probe_47 : ∀ (a b c: Point) (AB BC AC : Line),
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
  euclid_apply (line_from_points a d) as AD
  euclid_apply (line_from_points f c) as FC
  -- probe facts
  have p_bnec : b ≠ c := by euclid_finish
  have p_bned : b ≠ d := by euclid_finish
  have p_dnotAB : ¬(d.onLine AB) := by euclid_finish
  have p_ADneAB : AD ≠ AB := by euclid_finish
  have p_cnotBF : ¬(c.onLine BF) := by euclid_finish
  have p_FCneBF : FC ≠ BF := by euclid_finish
  have p_ABneAD : AB ≠ AD := by euclid_finish
  have p_lsdBC : l.sameSide d BC := by euclid_finish
  sorry

end Elements.Book1
