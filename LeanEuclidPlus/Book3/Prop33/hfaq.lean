import SystemE
import Book3.Prop33.hdaq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_33_hfaq
    (a b c₁ c c₂ d e0 f q : Point) (AB AD AE : Line)
    (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
    (h_a_AD : a.onLine AD) (h_d_AD : d.onLine AD)
    (h_de0 : ∠ d:a:e0 = ∟) (h_e0_AD : ¬ e0.onLine AD)
    (h_a_AE : a.onLine AE) (h_e0_AE : e0.onLine AE)
    (h_afb : between a f b)
    (h_q_AE : q.onLine AE) (h_qb : q.sameSide b AD)
    (h_dab : ∠ d:a:b = ∠ c₁:c:c₂) (h_da : d ≠ a)
    (hpos : 0 < ∠ c₁:c:c₂) (hlt : ∠ c₁:c:c₂ < ∟ + ∟) :
    ∠ f:a:q < ∟ := by
  -- ∠ d:a:q = ∟  (q on the perpendicular line AE ⊥ AD at a, either ray)
  have hdaq : ∠ d:a:q = ∟ := by euclid_apply (helper_3_33_hdaq a b d e0 q AD AE (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show ∠ d:a:e0 = ∟; assumption)) (by euclid_assumption "" (show ¬ e0.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e0.onLine AE; assumption)) (by euclid_assumption "" (show q.onLine AE; assumption)) (by euclid_assumption "" (show q.sameSide b AD; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)))
  -- ∠ f:a:q = ∠ b:a:q = |∠d:a:q − ∠d:a:b| < ∟, since q, b on the same side of AD
  euclid_finish

end Elements.Book3
