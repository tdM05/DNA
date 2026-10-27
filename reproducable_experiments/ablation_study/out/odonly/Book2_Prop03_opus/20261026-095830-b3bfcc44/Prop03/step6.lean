import SystemE
import Book1Variants.Prop34
import Book2.Prop03.step6_sfcd
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step6 (a b c d e f : Point) (AB CD DE BE AF : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    (hdCD : d.onLine CD) (hcCD : c.onLine CD)
    (hbcd : ∠ b:c:d = ∟) (hbed : ∠ b:e:d = ∟)
    (hbe_cb : |(b─e)| = |(c─b)|) (hde_cb : |(d─e)| = |(c─b)|)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hCDBE : ¬CD.intersectsLine BE)
    (heb : e ≠ b)
    (hDEAB : ¬DE.intersectsLine AB)
    (hAFCD : ¬AF.intersectsLine CD)
    (hacb : between a c b)
    (hstep2 : f.onLine DE ∧ between e d f)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(c─d)| = |(c─b)|) :   -- "$DC$ (is) equal to $CB$"
    Triangle.area △ a:f:d + Triangle.area △ a:d:c = |(a─c)| * |(c─b)| := by
  obtain ⟨_, hedf⟩ := hstep2
  have step6_sfcd : a.sameSide f CD := by euclid_apply (helper_2_3_step6_sfcd a b c d e f AB CD DE BE AF (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show f.onLine DE; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show ∠ b:c:d = ∟; assumption)) (by euclid_assumption "" (show ∠ b:e:d = ∟; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(b─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show |(d─e)| = |(c─b)|; assumption)) (by euclid_assumption "" (show a.onLine AF; assumption)) (by euclid_assumption "" (show f.onLine AF; assumption)) (by euclid_assumption "" (show ¬AF.intersectsLine CD; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  have hpara6 : formParallelogram a c f d AB DE AF CD := by euclid_finish
  euclid_apply (Elements.Book1.proposition_34' a c f d AB DE AF CD)
  have hangafd : ∠ a:f:d = ∟ := by euclid_finish
  euclid_apply (rectangle_area a c f d AB DE AF CD)
  have haf_cb : |(a─f)| = |(c─b)| := by euclid_finish
  have hrect6 : (△a:f:d).area + (△a:c:d).area = |(a─c)| * |(a─f)| := by euclid_finish
  have harea6 : (△a:d:c).area = (△a:c:d).area := by euclid_finish
  rw [harea6, hrect6, haf_cb]

end Elements.Book2
