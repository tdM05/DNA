import SystemE
import Helpers.SameSide
import Book1Variants.Prop34
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_38_s7
    (d e f h : Point) (AD BF DE FH DF : Line)
    (hd_AD : d.onLine AD) (hh_AD : h.onLine AD)
    (hh_FH : h.onLine FH) (hf_FH : f.onLine FH)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE) (hde : d ≠ e)
    (he_BF : e.onLine BF) (hf_BF : f.onLine BF)
    (hd_DF : d.onLine DF) (hf_DF : f.onLine DF)
    (hFH_DE : ¬FH.intersectsLine DE)
    (hAD_BF : ¬AD.intersectsLine BF)
    (hDE_BF : DE ≠ BF)
    (hassump1 : formParallelogram d e h f DE FH AD BF)
    : Triangle.area △ f:e:d + Triangle.area △ f:e:d =
      Triangle.area △ d:e:f + Triangle.area △ d:f:h := by

  have hh_off_DE : ¬h.onLine DE := by euclid_finish

  have hDE_FH : ¬DE.intersectsLine FH := fun h => hFH_DE (intersection_symm DE FH h)

  have hh_ss_f : h.sameSide f DE :=
    sameSide_of_parallel' h f h FH DE hh_FH hf_FH hh_FH hh_off_DE hFH_DE

  have hpgram : formParallelogram h d f e AD BF FH DE :=
    ⟨hh_AD, hd_AD, hf_BF, he_BF, hh_FH, hf_FH, ⟨hd_DE, he_DE, hde⟩, hh_ss_f, hAD_BF, hFH_DE⟩

  have hAD_ne_BF : AD ≠ BF := by euclid_finish

  have hdf : d ≠ f := fun heq =>
    hAD_BF (intersection_lines_common_point f AD BF ⟨heq ▸ hd_AD, hf_BF, hAD_ne_BF⟩)

  obtain ⟨-, -, -, -, h_area⟩ := proposition_34 h d f e AD BF FH DE DF
    ⟨hpgram, ⟨hd_DF, hf_DF, hdf⟩⟩
  linarith [area_symm_1 h d f, area_symm_1 d f h,
            area_symm_1 e f d, area_symm_1 f d e,
            area_symm_2 f e d, area_symm_2 d e f]

end Elements.Book1
