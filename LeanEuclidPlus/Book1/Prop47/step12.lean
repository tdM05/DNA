import SystemE
import Book1.Prop04.Main
import Book1.Prop47.step11_foffBC
import Book1.Prop47.step11_T1
import Book1.Prop47.step11_T2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step12
    (a b c d e f : Point) (AB BC AC BD BF AD FC : Line)
    (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hcFC : c.onLine FC) (hfFC : f.onLine FC)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hoffBD : ¬a.onLine BD) (haoffBC : ¬a.onLine BC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    (hbac : ∠ b:a:c = ∟) (habf : ∠ a:b:f = ∟)
    (hab : a ≠ b) (hfb : f ≠ b)
    (hce_len : |(c─e)| = |(b─c)|) (hec : e ≠ c)
    (hstep9 : |(d─b)| = |(c─b)| ∧ |(b─a)| = |(b─f)|)
    (hstep10 : ∠ d:b:a = ∠ f:b:c) (hstep11 : |(a─d)| = |(f─c)|) :
    Triangle.area △ a:b:d = Triangle.area △ f:b:c := by
  obtain ⟨h9a, h9b⟩ := hstep9
  have hbc : b ≠ c := by euclid_finish
  have hbd : b ≠ d := by euclid_finish
  have hcb : c ≠ b := Ne.symm hbc
  have had : a ≠ d := by euclid_finish
  have hdoffAB : ¬d.onLine AB := by euclid_finish
  have step11_foffBC : ¬f.onLine BC := by euclid_apply (helper_1_47_step11_foffBC a b c f AB BC AC BF (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show ∠ b:a:c = ∟; assumption)) (by euclid_assumption "" (show ∠ a:b:f = ∟; assumption)) (by euclid_assumption "" (show ¬a.onLine BC; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show c ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)))
  have hcoffBF : ¬c.onLine BF := by euclid_finish
  have hcf : c ≠ f := by euclid_finish
  have hboffFC : ¬b.onLine FC := by euclid_finish
  have step11_T1 : formTriangle b d a BD AD AB := by euclid_apply (helper_1_47_step11_T1 a b d AB BD AD (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show a.onLine AD; assumption)) (by euclid_assumption "" (show d.onLine AD; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show ¬a.onLine BD; assumption)) (by euclid_assumption "" (show ¬d.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show a ≠ d; assumption)))
  have step11_T2 : formTriangle b c f BC FC BF := by euclid_apply (helper_1_47_step11_T2 b c f BC FC BF (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine FC; assumption)) (by euclid_assumption "" (show f.onLine FC; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬f.onLine BC; assumption)) (by euclid_assumption "" (show ¬b.onLine FC; assumption)) (by euclid_assumption "" (show f ≠ b; assumption)) (by euclid_assumption "" (show c ≠ f; assumption)))
  euclid_apply (proposition_4 b d a b c f BD AD AB BC FC BF)
  euclid_apply (area_congruence a b d f b c)
  euclid_finish

end Elements.Book1
