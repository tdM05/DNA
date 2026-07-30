import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem h_1_44_s13_x1
    (a b f g h k l m : Point) (GF AH KL : Line)
    (hhGF : h.onLine GF) (hgGF : g.onLine GF)
    (hhAH : h.onLine AH) (hlAH : l.onLine AH)
    (hlKL : l.onLine KL) (hkKL : k.onLine KL)
    (s13_x4 : l ≠ k)
    (s13_x3 : ¬GF.intersectsLine KL)
    (hGFAH : GF.intersectsLine AH)
    (s12 : between h a l ∧ between f b m)
    : h.sameSide g KL := by
  have hhlne : h ≠ l := (between_symm h a l s12.1).2.2.1
  have hGFneKL : GF ≠ KL := by
    intro heq
    have hlGF : l.onLine GF := heq.symm ▸ hlKL
    have hGFeqAH : GF = AH :=
      two_points_determine_line h l GF AH ⟨⟨hhGF, hlGF, hhlne⟩, hhAH, hlAH⟩
    have hKLeqAH : KL = AH := heq.symm.trans hGFeqAH
    exact absurd hGFAH (hKLeqAH ▸ s13_x3)
  euclid_finish

end Elements.Book1
