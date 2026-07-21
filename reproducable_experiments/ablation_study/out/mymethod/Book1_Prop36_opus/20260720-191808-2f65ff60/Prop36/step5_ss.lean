import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- e.sameSide b CH.  Key: BG, CD, CH are concurrent at c, so triple_incidence_2
-- transfers the CD opposite-sides of b,h into b,d same side of CH.
theorem helper_1_36_step5_ss (a b c d e h : Point) (AH BG AB CD CH : Line)
    (ha_ah : a.onLine AH) (hd_ah : d.onLine AH) (he_ah : e.onLine AH) (hh_ah : h.onLine AH)
    (hb_bg : b.onLine BG) (hc_bg : c.onLine BG)
    (hh_ch : h.onLine CH) (hc_ch : c.onLine CH)
    (ha_ab : a.onLine AB) (hb_ab : b.onLine AB)
    (hd_cd : d.onLine CD) (hc_cd : c.onLine CD)
    (hdc : d ≠ c)
    (hsame_cd : a.sameSide b CD)
    (hadh : between a d h) (haeh : between a e h)
    (hpar : ¬AH.intersectsLine BG) (hpar2 : ¬AB.intersectsLine CD) :
    e.sameSide b CH := by
  have hne : AH ≠ BG := by euclid_finish
  have hc_off_ah : ¬c.onLine AH := by euclid_finish
  have hne2 : AH ≠ CH := by euclid_finish
  have he_off : ¬e.onLine CH := by euclid_finish
  have hd_off : ¬d.onLine CH := by euclid_finish
  -- e, d are on the same side of CH as a (h is CH's crossing of AH)
  have hea : e.sameSide a CH := by euclid_apply (pasch_2 h e a CH); euclid_finish
  have hda : d.sameSide a CH := by euclid_apply (pasch_2 h d a CH); euclid_finish
  -- d, h same side of BG (both on AH, AH ∥ BG)
  have hdh_bg : d.sameSide h BG := by euclid_finish
  -- a, h are on opposite sides of CD (d is between them and on CD)
  have hah_cd : ¬a.sameSide h CD := by euclid_apply (pasch_3 a d h CD); euclid_finish
  -- b is on a's side of CD, hence opposite h across CD
  have hbh_cd : ¬b.sameSide h CD := by euclid_finish
  have hh_off_cd : ¬h.onLine CD := by euclid_finish
  -- triple incidence at c (BG, CD, CH meet at c): b, d same side of CH
  have hbd : b.sameSide d CH := by
    euclid_apply (triple_incidence_2 BG CD CH c b d h)
    euclid_finish
  euclid_finish

end Elements.Book1
