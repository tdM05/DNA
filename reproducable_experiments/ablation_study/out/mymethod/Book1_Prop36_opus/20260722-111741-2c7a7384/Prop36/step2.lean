import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step2 (b c e f g h : Point) (AH BG EF HG : Line)
  (heAH : e.onLine AH) (hhAH : h.onLine AH) (hfBG : f.onLine BG) (hgBG : g.onLine BG)
  (heEF : e.onLine EF) (hfEF : f.onLine EF) (hhHG : h.onLine HG) (hgHG : g.onLine HG)
  (hhg : h ≠ g) (hssef : e.sameSide f HG)
  (hparAHBG : ¬AH.intersectsLine BG) (hparEFHG : ¬EF.intersectsLine HG)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : |(b─c)| = |(f─g)|)   -- "$BC$ is equal to $FG$"
  (hassump2 : |(f─g)| = |(e─h)|)   -- "$FG$ is equal to $EH$ [Prop.~1.34]"
  : |(b─c)| = |(e─h)| := by
  euclid_apply (line_from_points h f) as HF
  euclid_apply (proposition_34 e h f g AH BG EF HG HF)
  euclid_finish

end Elements.Book1
