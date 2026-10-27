import SystemE
import Mathlib.Tactic.Linarith
import Book2.Prop03.step7_par
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step7 (a b c d e : Point) (AB CD BE DE : Line)
    (hbetween : between a c b)
    (hc_AB : c.onLine AB) (hb_AB : b.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_CD_BE : ¬CD.intersectsLine BE)
    (hdc_BE : d.sameSide c BE)
    (h_bed : ∠ b:e:d = ∟)
    (h_cd_cb : |(c─d)| = |(c─b)|)
    (h_be_cb : |(b─e)| = |(c─b)|)
    (h_eb : e ≠ b) :
    Triangle.area △ c:d:e + Triangle.area △ c:e:b = |(b─c)| * |(b─c)| := by
  -- the square CDEB viewed with corner b: sides BC and BE
  have step7_par : formParallelogram b c e d AB DE BE CD := by euclid_apply (helper_2_3_step7_par a b c d e AB CD BE DE (by euclid_assumption "" (show between a c b; assumption)) (by euclid_assumption "" (show c.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine DE; assumption)) (by euclid_assumption "" (show e.onLine DE; assumption)) (by euclid_assumption "" (show b.onLine BE; assumption)) (by euclid_assumption "" (show e.onLine BE; assumption)) (by euclid_assumption "" (show ¬DE.intersectsLine AB; assumption)) (by euclid_assumption "" (show ¬CD.intersectsLine BE; assumption)) (by euclid_assumption "" (show d.sameSide c BE; assumption)) (by euclid_assumption "" (show |(c─d)| = |(c─b)|; assumption)) (by euclid_assumption "" (show e ≠ b; assumption)))
  -- square contained by BC and BE (right angle ∠ b:e:d given)
  have hpair := rectangle_area b c e d AB DE BE CD ⟨step7_par, h_bed⟩
  have heq2 := hpair.2
  -- heq2 : area△c:b:e + area△c:d:e = |b─c| * |b─e|
  have harea : Triangle.area (△ c:b:e) = Triangle.area (△ c:e:b) := area_symm_2 c b e
  rw [harea, h_be_cb, segment_symmetric c b] at heq2
  -- heq2 : area△c:e:b + area△c:d:e = |b─c| * |b─c|
  linarith [heq2]

end Elements.Book2
