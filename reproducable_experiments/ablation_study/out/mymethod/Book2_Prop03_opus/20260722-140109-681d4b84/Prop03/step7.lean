import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2
open Elements

theorem helper_2_3_step7 (a b c d e : Point) (AB CD DE BE : Line)
    (hbetacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcd_len : |(c─d)| = |(c─b)|) (hde_len : |(d─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟)
    (hCDparBE : ¬(CD.intersectsLine BE)) (hDEparAB : ¬(DE.intersectsLine AB)) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  euclid_intros
  have hcb : c ≠ b := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  have hde_ne : d ≠ e := by euclid_finish
  -- off-line facts via Helpers.OffLine
  have hdoffAB : ¬(d.onLine AB) := offLine_of_right_angle c b d AB hcAB hbAB hcb hcd_ne hbcd
  have haoffDE : ¬(a.onLine DE) := offLine_of_parallel a d AB DE haAB hdDE hdoffAB hDEparAB
  have hABneDE : AB ≠ DE := line_ne_of_offLine a AB DE haAB haoffDE
  have hABparDE : ¬(AB.intersectsLine DE) := fun h => hDEparAB (intersection_symm AB DE h)
  have hcsb : c.sameSide b DE :=
    sameSide_of_parallel_both c b AB DE hcAB hbAB hABneDE hABparDE
  -- square CDEB as a parallelogram anchored at c, right angle ∠c:b:e given
  have hpara : formParallelogram c d b e CD BE AB DE :=
    ⟨hcCD, hdCD, hbBE, heBE, hcAB, hbAB, ⟨hdDE, heDE, hde_ne⟩, hcsb, hCDparBE, hABparDE⟩
  obtain ⟨hc1, _⟩ := rectangle_area c d b e CD BE AB DE ⟨hpara, hcbe⟩
  -- hc1 : △c:b:e + △c:d:e = |(c─d)| * |(c─b)|
  have e1 : |(c─d)| = |(b─c)| := by euclid_finish
  have e2 : |(c─b)| = |(b─c)| := by euclid_finish
  have hprod : |(c─d)| * |(c─b)| = |(b─c)| * |(b─c)| := by rw [e1, e2]
  have harea : Triangle.area △ c:e:b = Triangle.area △ c:b:e := area_symm_2 c e b
  linarith [hc1, harea, hprod]

end Elements.Book2
