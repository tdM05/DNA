import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2
open Elements

theorem helper_2_3_step5 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (hbetacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hab_ne : a ≠ b)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (heb_ne : e ≠ b)
    (hcd_len : |(c─d)| = |(c─b)|) (hbe_len : |(b─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟) (hbed : ∠ b:e:d = ∟)
    (hAFparCD : ¬(AF.intersectsLine CD)) (hCDparBE : ¬(CD.intersectsLine BE))
    (hDEparAB : ¬(DE.intersectsLine AB))
    (hstep2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b = |(a─b)| * |(b─c)| := by
  euclid_intros
  obtain ⟨_, hedf⟩ := hstep2
  have hbef : ∠ b:e:f = ∟ := by euclid_finish
  have hcb : c ≠ b := by euclid_finish
  have hac_ne : a ≠ c := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  -- off-line facts via Helpers.OffLine
  have hdoffAB : ¬(d.onLine AB) := offLine_of_right_angle c b d AB hcAB hbAB hcb hcd_ne hbcd
  have heoffAB : ¬(e.onLine AB) := offLine_of_right_angle b c e AB hbAB hcAB (Ne.symm hcb) heb_ne.symm hcbe
  have haoffCD : ¬(a.onLine CD) :=
    offLine_of_two_points a c d AB CD haAB hcAB hac_ne hcCD hdCD hdoffAB
  have hboffCD : ¬(b.onLine CD) :=
    offLine_of_two_points b c d AB CD hbAB hcAB (Ne.symm hcb) hcCD hdCD hdoffAB
  have haoffBE : ¬(a.onLine BE) :=
    offLine_of_two_points a b e AB BE haAB hbAB hab_ne hbBE heBE heoffAB
  have haoffDE : ¬(a.onLine DE) := offLine_of_parallel a d AB DE haAB hdDE hdoffAB hDEparAB
  have haf_ne : a ≠ f := fun h => haoffDE (h ▸ hfDE)
  -- line-distinctness
  have hAFneCD : AF ≠ CD := line_ne_of_offLine a AF CD haAF haoffCD
  have hCDneBE : CD ≠ BE := (line_ne_of_offLine b BE CD hbBE hboffCD).symm
  have hAFneBE : AF ≠ BE := line_ne_of_offLine a AF BE haAF haoffBE
  have hBEneAF : BE ≠ AF := hAFneBE.symm
  -- AF ∥ BE, and b,e same side of AF
  have hAFparBE : ¬(AF.intersectsLine BE) :=
    not_intersects_trans AF CD BE hAFparCD hCDparBE hAFneCD hCDneBE hAFneBE
  have hBEparAF : ¬(BE.intersectsLine AF) := fun h => hAFparBE (intersection_symm BE AF h)
  have hbse : b.sameSide e AF :=
    sameSide_of_parallel_both b e BE AF hbBE heBE hBEneAF hBEparAF
  have hABparDE : ¬(AB.intersectsLine DE) := fun h => hDEparAB (intersection_symm AB DE h)
  -- rectangle AFEB anchored at b: |b─a| * |b─e| = |a─b| * |b─c|
  have hpara : formParallelogram b a e f AB DE BE AF :=
    ⟨hbAB, haAB, heDE, hfDE, hbBE, heBE, ⟨haAF, hfAF, haf_ne⟩, hbse, hABparDE, hBEparAF⟩
  obtain ⟨_, hc2⟩ := rectangle_area b a e f AB DE BE AF ⟨hpara, hbef⟩
  -- hc2 : △a:b:e + △a:f:e = |(b─a)| * |(b─e)|
  have hlen1 : |(a─b)| = |(b─a)| := by euclid_finish
  have hlen2 : |(b─c)| = |(b─e)| := by euclid_finish
  have harea : Triangle.area △ a:e:b = Triangle.area △ a:b:e := area_symm_2 a e b
  rw [hlen1, hlen2]
  linarith [hc2, harea]

end Elements.Book2
