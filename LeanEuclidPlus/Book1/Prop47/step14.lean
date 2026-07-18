import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step14_par
import Book1.Prop47.step14_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step14
    (a b c e f g : Point) (AB BC AC BF GF FC : Line)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hfBF : f.onLine BF) (hbBF : b.onLine BF)
    (hgGF : g.onLine GF) (hfGF : f.onLine GF)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcag : between c a g) (hgoffAB : ¬g.onLine AB)
    (hGFAB : ¬GF.intersectsLine AB)
    (hbac : ∠ b:a:c = ∟) (habf : ∠ a:b:f = ∟) (haoffBC : ¬a.onLine BC) (hboffAC : ¬b.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hab : a ≠ b) (hfb : f ≠ b)
    (hce_len : |(c─e)| = |(b─c)|) (hec : e ≠ c)
    (hassump1 : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC)) :
    Triangle.area △ a:g:f + Triangle.area △ a:f:b =
      Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  obtain ⟨_, _, hBFAC⟩ := hassump1
  have hbc : b ≠ c := by euclid_finish
  have hACBF : ¬AC.intersectsLine BF := by euclid_finish
  have step14_par : formParallelogram g a f b AC BF GF AB := by euclid_apply (helper_1_47_step14_par a b c f g AC BF GF AB (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine GF; assumption)) (by euclid_assumption "" (show f.onLine GF; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show between c a g; assumption)) (by euclid_assumption "" (show ¬g.onLine AB; assumption)) (by euclid_assumption "" (show ¬AC.intersectsLine BF; assumption)) (by euclid_assumption "" (show ¬GF.intersectsLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  have step14_tri : formTriangle c f b FC BF BC := by euclid_apply (helper_1_47_step14_tri b c f FC BF BC AC (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show ¬BF.intersectsLine AC; assumption)) (by euclid_assumption "" (show ¬b.onLine AC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)))
  euclid_apply (proposition_41 g f b a c AC BF GF AB FC BC)
  euclid_apply (parallelogram_area g a f b AC BF GF AB)
  euclid_finish

end Elements.Book1
