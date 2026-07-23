import SystemE
import Book1.Prop17.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_step6 (a b c d e g : Point) (AC DB AB AG : Line)
    (haAC : a.onLine AC) (hcAC : c.onLine AC) (hac : a ≠ c) (hbAC : ¬b.onLine AC)
    (hbet : between a d c) (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (hadb : ∠ a:d:b = ∟)
    (hga : g ≠ a) (hgAB : g.onLine AB ∨ g.sameSide d AB) (hgab : ∠ g:a:b = ∠ a:b:d)
    (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (heAG : e.onLine AG) (heDB : e.onLine DB) :
    ∠ b:a:e = ∠ a:b:d ∧ e ≠ a := by
  -- ∠abd < ∟ (right triangle abd), and g off AB, so g is on d's side of AB.
  euclid_apply (Elements.Book1.proposition_17 a b d AB DB AC)
  have hgsd : g.sameSide d AB := by
    rcases hgAB with h | h
    · exfalso; euclid_finish
    · exact h
  -- The Postulate-5 meeting point p of AG and DB lies on g's side of AB; by uniqueness of a
  -- transversal intersection p = e, so e is on g's ray from a, giving ∠bae = ∠bag = ∠abd.
  euclid_apply (lines_intersect g a b d AG AB DB) as p
  euclid_finish

end Elements.Book3
