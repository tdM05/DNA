import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Sentence 1.36.2 cites [Prop.~1.34] ("$FG$ is equal to $EH$"): proposition_34 on the EFGH
-- parallelogram (opposite sides equal) gives |(f─g)| = |(e─h)|; combined with the given |(b─c)| =
-- |(f─g)| it closes |(b─c)| = |(e─h)|. The 1.34 application lives in THIS sentence's cone so
-- criterion-3 is satisfied here (the gap have step2_assumption2 is a separate root).
theorem helper_1_36_step2 (b c e f g h : Point) (AH BG EF HG : Line)
    (he_AH : e.onLine AH) (hh_AH : h.onLine AH)
    (hf_BG : f.onLine BG) (hg_BG : g.onLine BG)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
    (hh_HG : h.onLine HG) (hg_HG : g.onLine HG) (hhg : h ≠ g)
    (hef_ss : e.sameSide f HG)
    (hAHBG : ¬AH.intersectsLine BG) (hEFHG : ¬EF.intersectsLine HG)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : |(b─c)| = |(f─g)|)   -- "$BC$ is equal to $FG$"
    (hassump2 : |(f─g)| = |(e─h)|)   -- "$FG$ is equal to $EH$ [Prop.~1.34]"
    : |(b─c)| = |(e─h)| := by
  euclid_apply (line_from_points h f) as HF
  euclid_apply (proposition_34 e h f g AH BG EF HG HF)
  euclid_finish

end Elements.Book1
