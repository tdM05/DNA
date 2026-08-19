import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.24.4: "a circle will cut another circle at more than two points." The neither-inside-nor-outside
-- ("miss") case gives, by segment_arc_crossing, a third crossing point g (≠ c,d) shared by AEB' and
-- CFD. Together with c, d (both on AEB' via a'=c, b'=d, and both on CFD) that is THREE distinct
-- shared points. Term-mode: inside/outside are opaque (no SMT case).
theorem helper_3_24_step4
  (a e b c f d a' e' b' : Point) (CD AB : Line) (AEB AEB' CFD : Circle)
  (ImgSegment : Point → Point) (ImgCircle : Circle → Circle)
  (h_ImgSeg_a : ImgSegment a = a') (h_ImgSeg_e : ImgSegment e = e') (h_ImgSeg_b : ImgSegment b = b')
  (h_ImgCircle_AEB : ImgCircle AEB = AEB')
  (h_a'c : a' = c) (step1 : ImgSegment b = d)
  (h_a'_AEB' : a'.onCircle AEB') (h_e'_AEB' : e'.onCircle AEB') (h_b'_AEB' : b'.onCircle AEB')
  (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD) (h_cd : c ≠ d)
  (h_e'_notCD : ¬ e'.onLine CD) (h_f_notCD : ¬ f.onLine CD)
  (h_c_CFD : c.onCircle CFD) (h_f_CFD : f.onCircle CFD) (h_d_CFD : d.onCircle CFD)
  (h_sameside : e'.sameSide f CD)
  : (¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside (CircularSegment.ofPoints c f d)
     ∧ ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d)) →
        ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
          p.onCircle (ImgCircle AEB) ∧ q.onCircle (ImgCircle AEB) ∧ r.onCircle (ImgCircle AEB) ∧
          p.onCircle CFD ∧ q.onCircle CFD ∧ r.onCircle CFD := by
  rintro ⟨hnin, hnout⟩
  rw [h_ImgSeg_a, h_ImgSeg_e, h_ImgSeg_b, h_a'c, (show b' = d from h_ImgSeg_b.symm.trans step1)] at hnin hnout
  have h_b'd : b' = d := h_ImgSeg_b.symm.trans step1
  have h_c_AEB' : c.onCircle AEB' := h_a'c ▸ h_a'_AEB'
  have h_d_AEB' : d.onCircle AEB' := h_b'd ▸ h_b'_AEB'
  have hfcs1 : formCircularSegment c e' d CD AEB' :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_e'_notCD, h_c_AEB', h_e'_AEB', h_d_AEB'⟩
  have hfcs2 : formCircularSegment c f d CD CFD :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_f_notCD, h_c_CFD, h_f_CFD, h_d_CFD⟩
  obtain ⟨g, hg_AEB', hg_CFD, hgc, hgd⟩ :=
    segment_arc_crossing e' c f d CD AEB' CFD ⟨hfcs1, hfcs2, h_sameside, hnin, hnout⟩
  rw [h_ImgCircle_AEB]
  exact ⟨c, d, g, h_cd, Ne.symm hgc, Ne.symm hgd,
    h_c_AEB', h_d_AEB', hg_AEB', h_c_CFD, h_d_CFD, hg_CFD⟩

end Elements.Book3
