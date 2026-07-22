import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2
open Elements

theorem helper_2_3_step6 (a b c d e f : Point) (AB CD DE AF : Line)
    (hbetacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hcd_len : |(c─d)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟)
    (hAFparCD : ¬(AF.intersectsLine CD)) (hDEparAB : ¬(DE.intersectsLine AB))
    (hstep2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  euclid_intros
  obtain ⟨_, hedf⟩ := hstep2
  have hcdf : ∠ c:d:f = ∟ := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hac_ne : a ≠ c := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  -- off-line facts via Helpers.OffLine
  have hdoffAB : ¬(d.onLine AB) := offLine_of_right_angle c b d AB hcAB hbAB hcb hcd_ne hbcd
  have haoffCD : ¬(a.onLine CD) :=
    offLine_of_two_points a c d AB CD haAB hcAB hac_ne hcCD hdCD hdoffAB
  have haoffDE : ¬(a.onLine DE) := offLine_of_parallel a d AB DE haAB hdDE hdoffAB hDEparAB
  have haf_ne : a ≠ f := fun h => haoffDE (h ▸ hfDE)
  -- line-distinctness and parallels
  have hAFneCD : AF ≠ CD := line_ne_of_offLine a AF CD haAF haoffCD
  have hCDneAF : CD ≠ AF := hAFneCD.symm
  have hCDparAF : ¬(CD.intersectsLine AF) := fun h => hAFparCD (intersection_symm CD AF h)
  have hcsd : c.sameSide d AF :=
    sameSide_of_parallel_both c d CD AF hcCD hdCD hCDneAF hCDparAF
  have hABparDE : ¬(AB.intersectsLine DE) := fun h => hDEparAB (intersection_symm AB DE h)
  -- rectangle AFDC anchored at c: |c─a| * |c─d| = |a─c| * |c─b|
  have hpara : formParallelogram c a d f AB DE CD AF :=
    ⟨hcAB, haAB, hdDE, hfDE, hcCD, hdCD, ⟨haAF, hfAF, haf_ne⟩, hcsd, hABparDE, hCDparAF⟩
  obtain ⟨_, hc2⟩ := rectangle_area c a d f AB DE CD AF ⟨hpara, hcdf⟩
  -- hc2 : △a:c:d + △a:f:d = |(c─a)| * |(c─d)|
  have hlen1 : |(a─c)| = |(c─a)| := by euclid_finish
  have hlen2 : |(c─b)| = |(c─d)| := by euclid_finish
  have harea : Triangle.area △ a:d:c = Triangle.area △ a:c:d := area_symm_2 a d c
  rw [hlen1, hlen2]
  linarith [hc2, harea]

end Elements.Book2
