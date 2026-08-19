import SystemE
import Book3.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.24.5: "The very thing is impossible [Prop.~3.10]." In the miss branch (hnot_inside/hnot_outside)
-- step4 hands us THREE distinct shared points of the moved circle (ImgCircle AEB = AEB') and CFD.
-- If those circles coincided, e' (on AEB') would lie on CFD — i.e. the segments coincide, against the
-- reductio supposition; so the circles are DISTINCT, and two distinct circles cannot share three
-- points [III.10 = proposition_10]. Contradiction.
theorem helper_3_24_step5
  (a e b c f d e' : Point) (AEB AEB' CFD : Circle)
  (ImgSegment : Point → Point) (ImgCircle : Circle → Circle)
  (h_ImgSeg_e : ImgSegment e = e')
  (h_ImgCircle_AEB : ImgCircle AEB = AEB')
  (h_e'_AEB' : e'.onCircle AEB')
  (step1_assumption1 : ImgSegment a = c)
  (step1 : ImgSegment b = d)
  (hsuppose1 : ¬(ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD))
  (hnot_inside  : ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside  (CircularSegment.ofPoints c f d))
  (hnot_outside : ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d))
  (step4 :
    (¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).inside (CircularSegment.ofPoints c f d)
     ∧ ¬ (CircularSegment.ofPoints (ImgSegment a) (ImgSegment e) (ImgSegment b)).outside (CircularSegment.ofPoints c f d)) →
        ∃ (p q r : Point), p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
          p.onCircle (ImgCircle AEB) ∧ q.onCircle (ImgCircle AEB) ∧ r.onCircle (ImgCircle AEB) ∧
          p.onCircle CFD ∧ q.onCircle CFD ∧ r.onCircle CFD)
  : False := by
  -- were the circles equal, e' (on AEB') would lie on CFD ⟹ coincidence ⟹ contradicts hsuppose1
  have hne : ImgCircle AEB ≠ CFD := by
    intro heq
    apply hsuppose1
    refine ⟨step1_assumption1, step1, ?_⟩
    rw [h_ImgSeg_e]
    have hAEB'_CFD : AEB' = CFD := h_ImgCircle_AEB.symm.trans heq
    exact hAEB'_CFD ▸ h_e'_AEB'
  -- three shared points of two distinct circles — impossible by III.10
  have hshared := step4 ⟨hnot_inside, hnot_outside⟩
  euclid_apply (proposition_10 (ImgCircle AEB) CFD hne)
  exact absurd hshared (by assumption)

end Elements.Book3
