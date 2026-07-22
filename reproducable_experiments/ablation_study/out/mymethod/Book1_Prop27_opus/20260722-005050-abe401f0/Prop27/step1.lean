import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_27_step1
  (a d e f b g : Point) (AE FD EF : Line)
  (h_a_AE : a.onLine AE) (h_e_AE : e.onLine AE)
  (h_f_FD : f.onLine FD) (h_d_FD : d.onLine FD)
  (h_e_EF : e.onLine EF) (h_f_EF : f.onLine EF) (h_ef : e ≠ f)
  (h_a_off : ¬a.onLine EF) (h_d_off : ¬d.onLine EF)
  (h_b_AE : b.onLine AE) (h_aeb : between a e b)
  (h_g_AE : g.onLine AE) (h_g_FD : g.onLine FD)
  (hassump1 : AE.intersectsLine FD)
  : g.sameSide b EF ∨ g.opposingSides b EF := by
  have hb_off : ¬b.onLine EF := by euclid_finish
  have hg_off : ¬g.onLine EF := by euclid_finish
  by_cases hs : g.sameSide b EF
  · exact Or.inl hs
  · exact Or.inr ⟨hg_off, hb_off, hs⟩

end Elements.Book1
