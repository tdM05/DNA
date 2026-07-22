import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step1
  (a d e f g b : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_EF : ¬a.onLine EF) (h_d_EF : ¬d.onLine EF)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD)
  (h_b_AE : b.onLine AE) (h_aeb : between a e b)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : AE.intersectsLine FD)   -- "For if not"
  : g.sameSide b EF ∨ g.opposingSides b EF := by
  by_cases hs : g.sameSide b EF
  · exact Or.inl hs
  · refine Or.inr ⟨?_, ?_, hs⟩
    · -- ¬g.onLine EF : g ∈ AE∩FD; if g ∈ EF then g = e (AE≠EF meet at e) and g = f (FD≠EF meet at f),
      -- contradicting e ≠ f.
      euclid_finish
    · -- ¬b.onLine EF : b ∈ AE, between a e b; if b ∈ EF then b = e, contradicting between a e b.
      euclid_finish

end Elements.Book1
