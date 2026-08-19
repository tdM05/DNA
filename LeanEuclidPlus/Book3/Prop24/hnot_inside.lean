import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- The moved segment (c e' d on AEB') does not NEST inside the target (c f d on CFD): they share the
-- chord CD, e' and f are on the same side, and being similar they subtend EQUAL inscribed angles
-- (∠c:e':d = ∠c:f:d). Equal angle ⟹ no nesting (segment_equal_angle_no_nest). Term-mode: inside is
-- opaque (no SMT case).
theorem helper_3_24_hnot_inside
  (a e b c f d a' e' b' : Point) (CD : Line) (AEB' CFD : Circle)
  (ImgSegment : Point → Point)
  (h_ImgSeg_a : ImgSegment a = a') (h_ImgSeg_e : ImgSegment e = e') (h_ImgSeg_b : ImgSegment b = b')
  (h_a'c : a' = c) (step1 : ImgSegment b = d)
  (h_a'_AEB' : a'.onCircle AEB') (h_e'_AEB' : e'.onCircle AEB') (h_b'_AEB' : b'.onCircle AEB')
  (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD) (h_cd : c ≠ d)
  (h_e'_notCD : ¬ e'.onLine CD) (h_f_notCD : ¬ f.onLine CD)
  (h_c_CFD : c.onCircle CFD) (h_f_CFD : f.onCircle CFD) (h_d_CFD : d.onCircle CFD)
  (h_sameside : e'.sameSide f CD)
  (h_angle_eq : (∠ a':e':b' : ℝ) = (∠ a:e:b)) (h_sim : (∠ a:e:b : ℝ) = (∠ c:f:d))
  : ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside
      (CircularSegment.ofPoints c f d) := by
  have h_b'd : b' = d := h_ImgSeg_b.symm.trans step1
  rw [h_ImgSeg_a, h_ImgSeg_e, h_ImgSeg_b, h_a'c, h_b'd]
  have h_c_AEB' : c.onCircle AEB' := h_a'c ▸ h_a'_AEB'
  have h_d_AEB' : d.onCircle AEB' := h_b'd ▸ h_b'_AEB'
  have hfcs1 : formCircularSegment c e' d CD AEB' :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_e'_notCD, h_c_AEB', h_e'_AEB', h_d_AEB'⟩
  have hfcs2 : formCircularSegment c f d CD CFD :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_f_notCD, h_c_CFD, h_f_CFD, h_d_CFD⟩
  have h_angle : (∠ c:e':d : ℝ) = (∠ c:f:d) := by
    conv_lhs => rw [← h_a'c, ← h_b'd]
    exact h_angle_eq.trans h_sim
  exact (segment_equal_angle_no_nest e' c f d CD AEB' CFD ⟨hfcs1, hfcs2, h_sameside, h_angle⟩).1

end Elements.Book3
