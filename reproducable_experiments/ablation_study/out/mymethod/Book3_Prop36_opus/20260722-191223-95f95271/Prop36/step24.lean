import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step24
  (a c d e f : Point) (ABC : Circle) (DA ED EF : Line)
  (ha_DA : a.onLine DA) (hd_DA : d.onLine DA) (hf_DA : f.onLine DA)
  (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF)
  (hbet : between d c a)
  (hecenter : e.isCentre ABC)
  (hnotthrough : ¬∃ p : Point, p.isCentre ABC ∧ p.onLine DA)
  (hstep17 : |(a─f)| = |(f─c)|)
  (hperp_all : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  : |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  have hnotDA : ¬ e.onLine DA := fun he => hnotthrough ⟨e, hecenter, he⟩
  have hdf : d ≠ f := by euclid_finish
  have hrt : ∠ d:f:e = ∟ := hperp_all d hd_DA hdf
  euclid_apply (Elements.Book1.proposition_47 f d e DA ED EF)
  euclid_finish

end Elements.Book3
