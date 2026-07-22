import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Parallel
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2
open Elements

theorem helper_2_3_step4 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (hbetacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hab_ne : a ≠ b)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (heb_ne : e ≠ b)
    (hcd_len : |(c─d)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcbe : ∠ c:b:e = ∟)
    (hAFparCD : ¬(AF.intersectsLine CD)) (hCDparBE : ¬(CD.intersectsLine BE))
    (hDEparAB : ¬(DE.intersectsLine AB))
    (hstep2 : f.onLine DE ∧ between e d f) :
    Triangle.area △ a:f:e + Triangle.area △ a:e:b =
      (Triangle.area △ a:f:d + Triangle.area △ a:d:c)
    + (Triangle.area △ c:d:e + Triangle.area △ c:e:b) := by
  euclid_intros
  obtain ⟨_, hedf⟩ := hstep2
  have hfde : between f d e := by euclid_finish
  -- small distinctness
  have hcb : c ≠ b := by euclid_finish
  have hac_ne : a ≠ c := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  -- off-line facts via Helpers.OffLine (zero SMT here)
  have hdoffAB : ¬(d.onLine AB) := offLine_of_right_angle c b d AB hcAB hbAB hcb hcd_ne hbcd
  have heoffAB : ¬(e.onLine AB) := offLine_of_right_angle b c e AB hbAB hcAB (Ne.symm hcb) heb_ne.symm hcbe
  have haoffCD : ¬(a.onLine CD) :=
    offLine_of_two_points a c d AB CD haAB hcAB hac_ne hcCD hdCD hdoffAB
  have hboffCD : ¬(b.onLine CD) :=
    offLine_of_two_points b c d AB CD hbAB hcAB (Ne.symm hcb) hcCD hdCD hdoffAB
  have haoffBE : ¬(a.onLine BE) :=
    offLine_of_two_points a b e AB BE haAB hbAB hab_ne hbBE heBE heoffAB
  -- line-distinctness (pure terms)
  have hAFneCD : AF ≠ CD := line_ne_of_offLine a AF CD haAF haoffCD
  have hCDneBE : CD ≠ BE := (line_ne_of_offLine b BE CD hbBE hboffCD).symm
  have hAFneBE : AF ≠ BE := line_ne_of_offLine a AF BE haAF haoffBE
  -- AF ∥ BE (both parallel to CD), and A,F same side of BE
  have hAFparBE : ¬(AF.intersectsLine BE) :=
    not_intersects_trans AF CD BE hAFparCD hCDparBE hAFneCD hCDneBE hAFneBE
  have hasf : a.sameSide f BE :=
    sameSide_of_parallel_both a f AF BE haAF hfAF hAFneBE hAFparBE
  have hABparDE : ¬(AB.intersectsLine DE) := fun h => hDEparAB (intersection_symm AB DE h)
  -- assemble the parallelogram AFEB and apply the area-sum axiom
  have hpara : formParallelogram a b f e AB DE AF BE :=
    ⟨haAB, hbAB, hfDE, heDE, haAF, hfAF, ⟨hbBE, heBE, heb_ne.symm⟩, hasf, hABparDE, hAFparBE⟩
  euclid_apply (sum_parallelograms_area a b f e c d AB DE AF BE)
  linarith

end Elements.Book2
