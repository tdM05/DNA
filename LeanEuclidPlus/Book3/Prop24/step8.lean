import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.24.8: "and will be equal to it [C.N.4]." The moved segment ⌓a':e':b' equals ⌓a:e:b by
-- superposition (area preserved), and with a'=c, b'=d it IS the segment ⌓c:e':d. That coincides
-- with the target ⌓c:f:d (same circle CFD, same chord CD, e' and f on the same side), so by C.N.4
-- (coincide_equal_area) the two have equal area. Term-mode: ⌓ is opaque to euclid_finish.
theorem helper_3_24_step8
  (a e b c f d a' e' b' : Point) (CD : Line) (AEB' CFD : Circle)
  (ImgSegment : Point → Point)
  (h_ImgSeg_a : ImgSegment a = a') (h_ImgSeg_e : ImgSegment e = e') (h_ImgSeg_b : ImgSegment b = b')
  (h_a'c : a' = c) (step1 : ImgSegment b = d)
  (h_a'_AEB' : a'.onCircle AEB') (h_e'_AEB' : e'.onCircle AEB') (h_b'_AEB' : b'.onCircle AEB')
  (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD) (h_cd : c ≠ d)
  (h_e'_notCD : ¬ e'.onLine CD) (h_f_notCD : ¬ f.onLine CD)
  (h_c_CFD : c.onCircle CFD) (h_f_CFD : f.onCircle CFD) (h_d_CFD : d.onCircle CFD)
  (h_sameside : e'.sameSide f CD)
  (h_area_sup : (⌓ a':e':b' : ℝ) = (⌓ a:e:b))
  (step2 : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD)
  : ⌓ a:e:b = ⌓ c:f:d := by
  have h_b'd : b' = d := h_ImgSeg_b.symm.trans step1
  -- the moved segment sits on CFD (coincidence): e' on CFD, c and d on CFD
  have h_e'_CFD : e'.onCircle CFD := by
    have := step2.2.2; rw [h_ImgSeg_e] at this; exact this
  -- both segments lie on the SAME circle CFD, chord CD; c=a', d=b' put c,d on CFD (already have)
  have hform1 : formCircularSegment c e' d CD CFD :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_e'_notCD, h_c_CFD, h_e'_CFD, h_d_CFD⟩
  have hform2 : formCircularSegment c f d CD CFD :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_f_notCD, h_c_CFD, h_f_CFD, h_d_CFD⟩
  -- the two segments coincide, so by C.N.4 they have equal area
  have hcoin : (CircularSegment.ofPoints c e' d).coincides (CircularSegment.ofPoints c f d) :=
    ⟨c, e', d, f, CD, CFD, rfl, rfl, hform1, hform2, h_sameside⟩
  have h_eq2 : (⌓ c:e':d : ℝ) = (⌓ c:f:d) := coincide_equal_area _ _ hcoin
  -- ⌓a:e:b = ⌓a':e':b' = ⌓c:e':d (a'=c, b'=d) = ⌓c:f:d
  have h_eq1 : (⌓ a:e:b : ℝ) = (⌓ c:e':d) := by
    rw [← h_area_sup, h_a'c, h_b'd]
  rw [h_eq1, h_eq2]

end Elements.Book3
