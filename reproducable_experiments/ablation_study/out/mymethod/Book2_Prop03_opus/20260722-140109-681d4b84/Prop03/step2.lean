import SystemE
import Helpers.OffLine
import Helpers.SameSide
import Helpers.Pasch
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2
open Elements

theorem helper_2_3_step2 (a b c d e f : Point) (AB CD DE AF BE : Line)
    (hbetacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hcd_len : |(c─d)| = |(c─b)|) (hde_len : |(d─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟)
    (hAFparCD : ¬(AF.intersectsLine CD)) (hCDparBE : ¬(CD.intersectsLine BE)) :
    f.onLine DE ∧ between e d f := by
  euclid_intros
  -- small point-distinctness facts
  have hcb : c ≠ b := by euclid_finish
  have hac_ne : a ≠ c := by euclid_finish
  have hcd_ne : c ≠ d := by euclid_finish
  have hde_ne : d ≠ e := by euclid_finish
  have hed_ne : e ≠ d := hde_ne.symm
  -- off-line facts via pre-proved Helpers.OffLine lemmas (zero SMT here)
  have hdoffAB : ¬(d.onLine AB) := offLine_of_right_angle c b d AB hcAB hbAB hcb hcd_ne hbcd
  have haoffCD : ¬(a.onLine CD) :=
    offLine_of_two_points a c d AB CD haAB hcAB hac_ne hcCD hdCD hdoffAB
  have hboffCD : ¬(b.onLine CD) :=
    offLine_of_two_points b c d AB CD hbAB hcAB (Ne.symm hcb) hcCD hdCD hdoffAB
  have hcoffDE : ¬(c.onLine DE) := by euclid_finish
  have heoffCD : ¬(e.onLine CD) :=
    offLine_of_two_points e d c DE CD heDE hdDE hed_ne hdCD hcCD hcoffDE
  have hdoffAF : ¬(d.onLine AF) := offLine_of_parallel d a CD AF hdCD haAF haoffCD hAFparCD
  have hfd_ne : f ≠ d := fun h => hdoffAF (h ▸ hfAF)
  -- line-distinctness (pure terms)
  have hAFneCD : AF ≠ CD := line_ne_of_offLine a AF CD haAF haoffCD
  have hBEneCD : BE ≠ CD := line_ne_of_offLine b BE CD hbBE hboffCD
  have hCDneDE : CD ≠ DE := line_ne_of_offLine c CD DE hcCD hcoffDE
  have hBEparCD : ¬(BE.intersectsLine CD) := fun h => hCDparBE (intersection_symm BE CD h)
  -- e and f are on opposite sides of CD
  have hfa : f.sameSide a CD := sameSide_of_parallel_both f a AF CD hfAF haAF hAFneCD hAFparCD
  have heb : e.sameSide b CD := sameSide_of_parallel_both e b BE CD heBE hbBE hBEneCD hBEparCD
  have hab_opp : ¬(a.sameSide b CD) := not_sameSide_of_between a c b CD hcCD hbetacb
  have hef : ¬(e.sameSide f CD) := by euclid_finish
  have hef_ne : e ≠ f := by euclid_finish
  have hbet : between e d f :=
    between_of_not_sameSide e d f CD DE hCDneDE hdCD hdDE heDE hfDE hed_ne hfd_ne hef_ne hef
  exact ⟨hfDE, hbet⟩

end Elements.Book2
