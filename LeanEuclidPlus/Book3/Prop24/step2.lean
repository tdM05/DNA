import SystemE
import Book3.Prop10.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.24.2: "if AB coincides with CD, the segment AEB will also coincide with CFD."
-- The coincidence has three parts: A↦C, B↦D (from step1 / the placement), and the moved arc point
-- e' lands on CFD. The last is the real content: the moved segment (c e' d on circle AEB') and the
-- target (c f d on CFD) share the chord CD, sit on the same side (e' sameSide f), and — being
-- SIMILAR — subtend equal inscribed angles (∠c:e':d = ∠c:f:d). Equal angle ⟹ neither nests
-- (segment_equal_angle_no_nest); not nesting ⟹ the two circles cross at a third point g
-- (segment_arc_crossing); so AEB' and CFD share THREE distinct points c, d, g — which by III.10
-- forces AEB' = CFD, hence e' (on AEB') is on CFD. inside/outside are opaque (no SMT case), so this
-- whole chain is term-mode, never euclid_finish.
theorem helper_3_24_step2
  (a e b c f d a' e' b' : Point) (CD : Line) (AEB' CFD : Circle)
  (ImgSegment : Point → Point)
  (h_ImgSeg_a : ImgSegment a = a') (h_ImgSeg_e : ImgSegment e = e') (h_ImgSeg_b : ImgSegment b = b')
  (h_a'c : a' = c)
  (step1 : ImgSegment b = d)
  (h_a'_AEB' : a'.onCircle AEB') (h_e'_AEB' : e'.onCircle AEB') (h_b'_AEB' : b'.onCircle AEB')
  (h_c_CD : c.onLine CD) (h_d_CD : d.onLine CD) (h_cd : c ≠ d)
  (h_e'_notCD : ¬ e'.onLine CD) (h_f_notCD : ¬ f.onLine CD)
  (h_c_CFD : c.onCircle CFD) (h_f_CFD : f.onCircle CFD) (h_d_CFD : d.onCircle CFD)
  (h_sameside : e'.sameSide f CD)
  (h_angle_eq : (∠ a':e':b' : ℝ) = (∠ a:e:b)) (h_sim : (∠ a:e:b : ℝ) = (∠ c:f:d))
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : (ImgSegment a).onLine CD ∧ (ImgSegment b).onLine CD)   -- "$AB$ coincides with $CD$"
  : ImgSegment a = c ∧ ImgSegment b = d ∧ (ImgSegment e).onCircle CFD := by
  refine ⟨h_ImgSeg_a.trans h_a'c, step1, ?_⟩
  rw [h_ImgSeg_e]
  -- b' = d (moved endpoint coincides with D)
  have h_b'd : b' = d := h_ImgSeg_b.symm.trans step1
  -- c and d lie on the moved circle AEB' (a' = c, b' = d)
  have h_c_AEB' : c.onCircle AEB' := h_a'c ▸ h_a'_AEB'
  have h_d_AEB' : d.onCircle AEB' := h_b'd ▸ h_b'_AEB'
  -- the two similar segments on the common chord CD
  have hfcs1 : formCircularSegment c e' d CD AEB' :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_e'_notCD, h_c_AEB', h_e'_AEB', h_d_AEB'⟩
  have hfcs2 : formCircularSegment c f d CD CFD :=
    ⟨⟨h_c_CD, h_d_CD, h_cd⟩, h_f_notCD, h_c_CFD, h_f_CFD, h_d_CFD⟩
  -- equal inscribed angle ∠c:e':d = ∠c:f:d (moved segment is similar to target).
  -- ∠a':e':b' = ∠a:e:b = ∠c:f:d, and a'=c, b'=d rewrite the moved angle to ∠c:e':d.
  have h_angle : (∠ c:e':d : ℝ) = (∠ c:f:d) := by
    conv_lhs => rw [← h_a'c, ← h_b'd]
    exact h_angle_eq.trans h_sim
  -- equal angle ⟹ no nesting ⟹ the circles cross at a third point g
  have hnonest := segment_equal_angle_no_nest e' c f d CD AEB' CFD ⟨hfcs1, hfcs2, h_sameside, h_angle⟩
  have hcross := segment_arc_crossing e' c f d CD AEB' CFD ⟨hfcs1, hfcs2, h_sameside, hnonest.1, hnonest.2⟩
  obtain ⟨g, hg_AEB', hg_CFD, hgc, hgd⟩ := hcross
  -- three shared points c, d, g ⟹ (III.10) the two circles coincide
  have hcirc_eq : AEB' = CFD := by
    by_contra hne
    exact proposition_10 AEB' CFD hne
      ⟨c, d, g, h_cd, hgc.symm, hgd.symm, h_c_AEB', h_d_AEB', hg_AEB', h_c_CFD, h_d_CFD, hg_CFD⟩
  rw [← hcirc_eq]; exact h_e'_AEB'

end Elements.Book3
