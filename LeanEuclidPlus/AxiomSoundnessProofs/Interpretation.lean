import AxiomSoundnessProofs.Interpretation.Primitives
import AxiomSoundnessProofs.Interpretation.Helpers
import AxiomSoundnessProofs.Interpretation.Relations
import AxiomSoundnessProofs.Interpretation.Angles
import AxiomSoundnessProofs.Interpretation.Segments
import AxiomSoundnessProofs.Interpretation.Triangles
import AxiomSoundnessProofs.Interpretation.Arcs
import AxiomSoundnessProofs.Interpretation.CircularSegments

/-!
# ℝ² interpretation of System E — aggregator

The interpretation `I` of the System-E signature into ℝ², one file per `SystemE/Theory/` module:

- `Interpretation/Primitives.lean`      — `Point`, `Line`, `Circle`
- `Interpretation/Relations.lean`       — `onLine`, `sameSide`, `collinear`, `between`,
                                           `onCircle`, `insideCircle`, `isCentre`, the three
                                           `intersects*`, `distinctPointsOnLine`
- `Interpretation/Angles.lean`          — `Angle.degree`, `Angle.Right`
- `Interpretation/Segments.lean`        — `Segment.length`
- `Interpretation/Triangles.lean`       — `Triangle.area`
- `Interpretation/Arcs.lean`            — `Arc.measure` (provisional)
- `Interpretation/CircularSegments.lean`— `CircularSegment.area`, `.inside`, `.outside`
- `Interpretation/Helpers.lean`         — shared ℝ² math (interprets NO primitive)

Axiom soundness proofs live in `AxiomSoundnessProofs/Proofs/`.
-/
