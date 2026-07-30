import SystemE
import Book1.Prop41.Main
import Book1.Prop47.step14_pgram
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_47_s14
    (a b c f g : Point) (AB AC AG BF GF FC BC : Line)
    (hg_AG : g.onLine AG) (ha_AG : a.onLine AG)
    (hf_BF : f.onLine BF) (hb_BF : b.onLine BF)
    (hg_GF : g.onLine GF) (hf_GF : f.onLine GF)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hc_FC : c.onLine FC) (hf_FC : f.onLine FC)
    (hb_BC : b.onLine BC) (hc_BC : c.onLine BC)
    (hg_nAB : ¬g.onLine AB)
    (h_nAGBF : ¬AG.intersectsLine BF) (h_nGFAB : ¬GF.intersectsLine AB)
    (h_cag : between c a g)
    (hassump1 : f.onLine BF ∧ b.onLine BF ∧ ¬(BF.intersectsLine AC)) :
    Triangle.area △ a:g:f + Triangle.area △ a:f:b = Triangle.area △ f:b:c + Triangle.area △ f:b:c := by
  obtain ⟨_, _, h_nBFAC⟩ := hassump1
  have s14_x2 : formParallelogram g a f b AG BF GF AB := by euclid_apply (h_1_47_s14_x1 a b f g AG BF GF AB (by (show g.onLine AG; assumption)) (by (show a.onLine AG; assumption)) (by (show f.onLine BF; assumption)) (by (show b.onLine BF; assumption)) (by (show g.onLine GF; assumption)) (by (show f.onLine GF; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show a ≠ b; assumption)) (by (show ¬g.onLine AB; assumption)) (by (show ¬AG.intersectsLine BF; assumption)) (by (show ¬GF.intersectsLine AB; assumption)))
  euclid_apply (proposition_41 g f b a c AG BF GF AB FC BC)
  euclid_apply (parallelogram_area g a f b AG BF GF AB)
  euclid_finish

end Elements.Book1
