import SystemE
import Book1.Prop47.Main
import Book3.Prop03.Main

namespace Elements.Book3

-- The perpendicular $EF$ from the centre $E$ meets the chord $AC$ at its foot $F$.  Prop.~1.12
-- returns $F$ together with the determinacy `hdet` (every point of $DA$ other than $F$ subtends a
-- right-angle at $F$ with $E$).  We first show (via Pythagoras, Prop.~1.47) that $F$ lies strictly
-- inside the circle, hence $F$ is between the chord endpoints $A$ and $C$ — the diagrammatic fact
-- Euclid takes for granted before citing Prop.~3.3 to conclude $AF = FC$.
theorem helper_3_36_step17 (a c d e f : Point) (ABC : Circle) (DA EF : Line)
    (hasm : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    (h2 : a.onCircle ABC) (h3 : c.onCircle ABC)
    (h5 : f.onLine DA) (h6 : a.onLine DA) (hd : d.onLine DA)
    (h7 : between d c a)
    (hdet : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟) :
    |(a─f)| = |(f─c)| := by
  obtain ⟨h1, hef, hoff, _⟩ := hasm
  have hc : c.onLine DA := by euclid_finish
  have hac : a ≠ c := by euclid_finish
  -- $A \ne F$: otherwise $\angle CFE$ is a right-angle and Pythagoras forces $CA = 0$.
  have haf : a ≠ f := by
    intro he
    have hcr : ∠ c:f:e = ∟ := hdet c hc (fun hcf => hac (he.trans hcf.symm))
    euclid_apply (line_from_points c f) as CF
    euclid_apply (line_from_points f e) as FE0
    euclid_apply (line_from_points c e) as CE0
    euclid_apply (Elements.Book1.proposition_47 f c e CF CE0 FE0)
    euclid_finish
  have hra : ∠ a:f:e = ∟ := hdet a h6 haf
  euclid_apply (line_from_points a f) as AF
  euclid_apply (line_from_points f e) as FE
  euclid_apply (line_from_points a e) as AE
  euclid_apply (Elements.Book1.proposition_47 f a e AF AE FE)
  -- $F$ is inside the circle, hence between $A$ and $C$ on the chord line.
  have hbtw : between a f c := by euclid_finish
  euclid_apply (Elements.Book3.proposition_3 a c e f ABC DA EF)
  euclid_finish

end Elements.Book3
