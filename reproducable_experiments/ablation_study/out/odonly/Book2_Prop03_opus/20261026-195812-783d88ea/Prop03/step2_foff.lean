import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step2_foff (a b c d e f : Point) (AB CD BE DE AF : Line)
    (hbetween : between a c b)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hc_AB : c.onLine AB)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (ha_AF : a.onLine AF) (hf_AF : f.onLine AF)
    (h_AF_CD : ¬AF.intersectsLine CD)
    (hdc_BE : d.sameSide c BE)
    (h_DE_AB : ¬DE.intersectsLine AB)
    (h_eb : e ≠ b) (h_ab : a ≠ b) :
    ¬f.onLine CD := by
  -- DE ≠ AB (see step2_coff_de reasoning)
  have hDEne : DE ≠ AB := by
    intro h
    rw [h] at hd_DE he_DE
    euclid_apply (two_points_determine_line e b BE AB)
    euclid_finish
  -- d is off AB (d ∈ DE, DE meets AB nowhere)
  have hd_off_AB : ¬d.onLine AB := by
    intro hd
    euclid_apply (intersection_lines_common_point d DE AB)
    euclid_finish
  -- CD ≠ AB (d ∈ CD, d ∉ AB)
  have hCDne : CD ≠ AB := by intro h; rw [h] at hd_CD; exact hd_off_AB hd_CD
  -- a is off CD (else a,c on CD ∩ AB with a ≠ c ⟹ CD = AB)
  have ha_off : ¬a.onLine CD := by
    intro ha
    euclid_apply (two_points_determine_line a c AB CD)
    euclid_finish
  -- AF ≠ CD (a ∈ AF, a ∉ CD)
  have hAFne : AF ≠ CD := by intro h; rw [h] at ha_AF; exact ha_off ha_AF
  -- f on CD would put f ∈ CD ∩ AF ⟹ AF meets CD
  intro hf
  euclid_apply (intersection_lines_common_point f CD AF)
  euclid_finish

end Elements.Book2
