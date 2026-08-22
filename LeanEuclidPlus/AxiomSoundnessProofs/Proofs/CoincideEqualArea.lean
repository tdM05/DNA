import AxiomSoundnessProofs.Interpretation
import AxiomSoundnessProofs.Proofs.VectorLemmas

/-!
# Soundness of `coincide_equal_area` in ℝ²

Verbatim System-E axiom (SystemE/Theory/Inferences/Diagrammatic.lean), fully unfolded through
`coincides` / `formCircularSegment`:

```
axiom coincide_equal_area : ∀ (s t : CircularSegment), s.coincides t → (s : ℝ) = (t : ℝ)
```
where `s.coincides t` unfolds to: ∃ c e d f CD γ,
  s = ofPoints c e d ∧ t = ofPoints c f d ∧
  formCircularSegment c e d CD γ ∧ formCircularSegment c f d CD γ ∧ e.sameSide f CD,
and `formCircularSegment a e b AB AEB` unfolds to
  distinctPointsOnLine a b AB ∧ ¬ e.onLine AB ∧ a.onCircle AEB ∧ e.onCircle AEB ∧ b.onCircle AEB.

Under the interpretation `I` this is the ℝ² statement `coincide_equal_area` below.  We show the
two segment regions are the IDENTICAL set, so their areas are equal.  Content: (1) three concyclic
non-collinear points determine the SAME disk (circumcircle uniqueness); (2) same chord + same side
⟹ same half-plane.
-/

namespace RInterp

open MeasureTheory

/-- **Line bridge.** If `c,d` are distinct points on line `L` and `c,e,d` are collinear, then
`e` is on `L` too.  (A line through two distinct points is unique.) -/
lemma onLine_of_collinear {L : Line} {c d e : Pt}
    (hc : onLine c L) (hd : onLine d L) (hcd : c ≠ d) (hcol : collinear c e d) :
    onLine e L := by
  unfold onLine ℓ dot at *
  unfold collinear cross at hcol
  simp only [Prod.fst_sub, Prod.snd_sub] at hcol
  have hstar : L.a * (d.1 - c.1) + L.b * (d.2 - c.2) = 0 := by linarith
  have h1 : (L.a * (e.1 - c.1) + L.b * (e.2 - c.2)) * (d.1 - c.1) = 0 := by
    linear_combination (e.1 - c.1) * hstar - L.b * hcol
  have h2 : (L.a * (e.1 - c.1) + L.b * (e.2 - c.2)) * (d.2 - c.2) = 0 := by
    linear_combination (e.2 - c.2) * hstar + L.a * hcol
  have hne : d.1 - c.1 ≠ 0 ∨ d.2 - c.2 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hcd
    have e1 : c.1 = d.1 := by linarith [h.1]
    have e2 : c.2 = d.2 := by linarith [h.2]
    exact Prod.ext_iff.mpr ⟨e1, e2⟩
  have hg0 : L.a * (e.1 - c.1) + L.b * (e.2 - c.2) = 0 := by
    rcases hne with h | h
    · exact (mul_eq_zero.mp h1).resolve_right h
    · exact (mul_eq_zero.mp h2).resolve_right h
  linarith [hg0]

/-- The circle's centre `γ.c` is equidistant from any three points on `γ`. -/
lemma equidistant_center {a b c : Pt} {γ : Circle}
    (ha : onCircle a γ) (hb : onCircle b γ) (hc : onCircle c γ) :
    Equidistant a b c γ.c := by
  unfold onCircle dot at ha hb hc
  simp only [Prod.fst_sub, Prod.snd_sub] at ha hb hc
  refine ⟨?_, ?_⟩ <;>
    simp only [Equidistant, dot, Prod.fst_sub, Prod.snd_sub] <;> nlinarith [ha, hb, hc]

/-- Three concyclic non-collinear points have circumcentre = the circle's centre.
The centre `γ.c` is equidistant (`equidistant_center`), and the circumcentre is the UNIQUE
equidistant point, so they coincide — no coordinate formula needed. -/
lemma circumcenter_eq {a b c : Pt} {γ : Circle}
    (hnc : ¬ collinear a b c)
    (ha : onCircle a γ) (hb : onCircle b γ) (hc : onCircle c γ) :
    (exists_unique_circumcenter a b c hnc).choose = γ.c := by
  have hspec := (exists_unique_circumcenter a b c hnc).choose_spec
  exact (exists_unique_circumcenter a b c hnc).unique hspec.1
    (equidistant_center ha hb hc)

/-- For a non-collinear triple on `γ`, the disk through `a,b,c` is exactly `γ`'s closed disk. -/
lemma diskOf_eq {a b c : Pt} {γ : Circle}
    (hnc : ¬ collinear a b c)
    (ha : onCircle a γ) (hb : onCircle b γ) (hc : onCircle c γ) :
    diskOf a b c hnc = { p : Pt | dot (p - γ.c) (p - γ.c) ≤ γ.r^2 } := by
  unfold diskOf
  rw [circumcenter_eq hnc ha hb hc]
  ext p
  simp only [Set.mem_setOf_eq]
  -- radius² = ‖a − γ.c‖², from `ha`
  have hr : dot (a - γ.c) (a - γ.c) = γ.r^2 := ha
  rw [hr]

/-- **Proportionality bridge.** `chordForm c d` (the region's chord form, built from the two
endpoints) and `ℓ CD` (the line's own affine form) represent the same line, hence are proportional
by a nonzero scalar. -/
lemma chordForm_proportional {CD : Line} {c d : Pt}
    (hc : onLine c CD) (hd : onLine d CD) (hcd : c ≠ d) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∀ p, chordForm c d p = κ * ℓ CD p := by
  unfold onLine ℓ dot at hc hd
  have star : CD.a * (d.1 - c.1) + CD.b * (d.2 - c.2) = 0 := by linarith
  rcases CD.nondeg with ha | hb
  · have hu2 : d.2 - c.2 ≠ 0 := by
      intro h
      apply hcd
      have hu1 : d.1 - c.1 = 0 := by
        have : CD.a * (d.1 - c.1) = 0 := by rw [h] at star; linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' ha
        · exact h'
      have e1 : c.1 = d.1 := by linarith
      have e2 : c.2 = d.2 := by linarith
      exact Prod.ext_iff.mpr ⟨e1, e2⟩
    refine ⟨(d.2 - c.2) / CD.a, div_ne_zero hu2 ha, ?_⟩
    intro p
    unfold chordForm ℓ cross dot
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination (-(p.2 - c.2)) * star - (d.2 - c.2) * hc
  · have hu1 : d.1 - c.1 ≠ 0 := by
      intro h
      apply hcd
      have hu2 : d.2 - c.2 = 0 := by
        have : CD.b * (d.2 - c.2) = 0 := by rw [h] at star; linarith
        rcases mul_eq_zero.mp this with h' | h'
        · exact absurd h' hb
        · exact h'
      have e1 : c.1 = d.1 := by linarith
      have e2 : c.2 = d.2 := by linarith
      exact Prod.ext_iff.mpr ⟨e1, e2⟩
    refine ⟨-(d.1 - c.1) / CD.b, div_ne_zero (neg_ne_zero.mpr hu1) hb, ?_⟩
    intro p
    unfold chordForm ℓ cross dot
    simp only [Prod.fst_sub, Prod.snd_sub]
    rw [div_mul_eq_mul_div, eq_div_iff hb]
    linear_combination (p.1 - c.1) * star + (d.1 - c.1) * hc

/-- If `E` and `F` have the same (strict) sign, then `P·E ≥ 0 ↔ P·F ≥ 0` for any `P`. -/
lemma sign_iff {P E F : ℝ} (h : 0 < E * F) : (0 ≤ P * E ↔ 0 ≤ P * F) := by
  have hE2 : 0 < E * E := mul_self_pos.mpr (fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl 0 h)
  have hF2 : 0 < F * F := mul_self_pos.mpr (fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl 0 h)
  constructor
  · intro hPE
    have h2 : 0 ≤ (P * F) * (E * E) := by
      have e : (P * F) * (E * E) = (P * E) * (E * F) := by ring
      rw [e]; exact mul_nonneg hPE (le_of_lt h)
    have h3 : (0 : ℝ) * (E * E) ≤ (P * F) * (E * E) := by rw [zero_mul]; exact h2
    exact le_of_mul_le_mul_right h3 hE2
  · intro hPF
    have h2 : 0 ≤ (P * E) * (F * F) := by
      have e : (P * E) * (F * F) = (P * F) * (E * F) := by ring
      rw [e]; exact mul_nonneg hPF (le_of_lt h)
    have h3 : (0 : ℝ) * (F * F) ≤ (P * E) * (F * F) := by rw [zero_mul]; exact h2
    exact le_of_mul_le_mul_right h3 hF2

/-- Same chord + same side ⟹ same half-plane. -/
lemma halfOf_eq {CD : Line} {c e d f : Pt}
    (hc : onLine c CD) (hd : onLine d CD) (hcd : c ≠ d)
    (hss : sameSide e f CD) :
    halfOf c e d = halfOf c f d := by
  obtain ⟨κ, hκ0, hκ⟩ := chordForm_proportional hc hd hcd
  have hsign : 0 < chordForm c d e * chordForm c d f := by
    rw [hκ e, hκ f]
    have e : κ * ℓ CD e * (κ * ℓ CD f) = κ^2 * (ℓ CD e * ℓ CD f) := by ring
    rw [e]
    exact mul_pos (by positivity) hss
  unfold halfOf
  ext p
  simp only [Set.mem_setOf_eq, ge_iff_le]
  exact sign_iff hsign

/-- **Soundness of `coincide_equal_area` in ℝ².**  The two segment regions are the identical set,
so they have equal area. -/
theorem coincide_equal_area
    (c e d f : Pt) (CD : Line) (γ : Circle)
    -- formCircularSegment c e d CD γ :
    (hcd  : distinctPointsOnLine c d CD)
    (he   : ¬ onLine e CD)
    (hcγ  : onCircle c γ) (heγ : onCircle e γ) (hdγ : onCircle d γ)
    -- formCircularSegment c f d CD γ :
    (hf   : ¬ onLine f CD)
    (hfγ  : onCircle f γ)
    -- e.sameSide f CD :
    (hss  : sameSide e f CD) :
    (CircularSegment.ofPoints c e d).area = (CircularSegment.ofPoints c f d).area := by
  obtain ⟨hcL, hdL, hcd'⟩ := hcd
  -- both triples are non-collinear (arc point off the chord ⟹ not on line(c,d))
  have hnce : ¬ collinear c e d := fun hcol => he (onLine_of_collinear hcL hdL hcd' hcol)
  have hncf : ¬ collinear c f d := fun hcol => hf (onLine_of_collinear hcL hdL hcd' hcol)
  -- the two regions coincide
  have hregion : (CircularSegment.ofPoints c e d).region
      = (CircularSegment.ofPoints c f d).region := by
    unfold CircularSegment.region CircularSegment.ofPoints
    rw [dif_neg hnce, dif_neg hncf,
        diskOf_eq hnce hcγ heγ hdγ, diskOf_eq hncf hcγ hfγ hdγ,
        halfOf_eq hcL hdL hcd' hss]
  unfold CircularSegment.area
  rw [hregion]

end RInterp
