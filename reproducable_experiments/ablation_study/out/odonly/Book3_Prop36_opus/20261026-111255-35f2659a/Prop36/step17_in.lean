import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step17_in (a c d e f : Point) (ABC : Circle) (DA EF : Line)
  (haC : a.onCircle ABC) (hcC : c.onCircle ABC)
  (haDA : a.onLine DA) (hdDA : d.onLine DA) (hfDA : f.onLine DA)
  (heEF : e.onLine EF) (hfEF : f.onLine EF)
  (hdca : between d c a)
  (hperpall : ∀ p : Point, p.onLine DA → p ≠ f → ∠ p:f:e = ∟)
  (hassump1 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟)) :
    f.insideCircle ABC := by
  have he : e.isCentre ABC := hassump1.1
  have hcDA : c.onLine DA := by euclid_finish
  by_cases haf : a = f
  · have hcf : c ≠ f := by euclid_finish
    have hcfe : ∠ c:f:e = ∟ := hperpall c hcDA hcf
    euclid_apply (line_from_points c e) as CE
    euclid_apply (Elements.Book1.proposition_47 f c e DA CE EF (by euclid_finish))
    euclid_finish
  · have hafe : ∠ a:f:e = ∟ := hperpall a haDA haf
    euclid_apply (line_from_points a e) as AE
    euclid_apply (Elements.Book1.proposition_47 f a e DA AE EF (by euclid_finish))
    euclid_finish

end Elements.Book3
