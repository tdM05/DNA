import SystemE
import Book1.Prop03.Main
import Book1.Prop20.step10_bet
import Book1.Prop20.step10_iso
import Book1.Prop20.step10_gt
import Book1.Prop20.step10_form
import Book1.Prop20.step10_big
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_20_step10 (a b c : Point) (AB BC AC : Line)
    (h_aAB : a.onLine AB) (h_bAB : b.onLine AB) (h_ab : a ≠ b)
    (h_bBC : b.onLine BC) (h_cBC : c.onLine BC)
    (h_cAC : c.onLine AC) (h_aAC : a.onLine AC)
    (h_ABBC : AB ≠ BC) (h_BCAC : BC ≠ AC) (h_ACAB : AC ≠ AB) :
    |(b─c)| + |(c─a)| > |(a─b)| := by
  euclid_apply (extend_point_longer BC b c (c─a)) as d3'
  euclid_apply (proposition_3 c d3' c a BC AC) as d3
  euclid_apply (line_from_points d3 a) as D3A
  have step10_bet : between b c d3 := by euclid_apply (helper_1_20_step10_bet b c d3 d3' BC (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d3'.onLine BC; assumption)) (by euclid_assumption "" (show between b c d3'; assumption)) (by euclid_assumption "" (show between c d3 d3'; assumption)))
  have step10_iso : ∠ c:d3:a = ∠ c:a:d3 := by euclid_apply (helper_1_20_step10_iso a b c d3 d3' AB BC AC D3A (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d3'.onLine BC; assumption)) (by euclid_assumption "" (show between b c d3'; assumption)) (by euclid_assumption "" (show between c d3 d3'; assumption)) (by euclid_assumption "" (show d3.onLine D3A; assumption)) (by euclid_assumption "" (show a.onLine D3A; assumption)) (by euclid_assumption "" (show |(c─d3)| = |(c─a)|; assumption)))
  have step10_gt : ∠ b:a:d3 > ∠ b:d3:a := by euclid_apply (helper_1_20_step10_gt a b c d3 d3' AB BC AC D3A (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d3'.onLine BC; assumption)) (by euclid_assumption "" (show between c d3 d3'; assumption)) (by euclid_assumption "" (show d3.onLine D3A; assumption)) (by euclid_assumption "" (show a.onLine D3A; assumption)) (by euclid_assumption "" (show between b c d3; assumption)) (by euclid_assumption "" (show ∠ c:d3:a = ∠ c:a:d3; assumption)))
  have step10_form : formTriangle b a d3 AB D3A BC := by euclid_apply (helper_1_20_step10_form a b c d3 d3' AB BC AC D3A (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine AC; assumption)) (by euclid_assumption "" (show a.onLine AC; assumption)) (by euclid_assumption "" (show AB ≠ BC; assumption)) (by euclid_assumption "" (show BC ≠ AC; assumption)) (by euclid_assumption "" (show AC ≠ AB; assumption)) (by euclid_assumption "" (show d3'.onLine BC; assumption)) (by euclid_assumption "" (show between b c d3'; assumption)) (by euclid_assumption "" (show between c d3 d3'; assumption)) (by euclid_assumption "" (show d3.onLine D3A; assumption)) (by euclid_assumption "" (show a.onLine D3A; assumption)))
  have step10_big : |(b─d3)| > |(b─a)| := by euclid_apply (helper_1_20_step10_big a b d3 AB BC D3A (by euclid_assumption "" (show formTriangle b a d3 AB D3A BC; assumption)) (by euclid_assumption "" (show ∠ b:a:d3 > ∠ b:d3:a; assumption)))
  euclid_finish

end Elements.Book1
