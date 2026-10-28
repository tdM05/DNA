import SystemE
-- Proposition citations: import Book1.PropNN.Main / Book2.PropNN.Main / Book3.PropNN.Main — NOT Book.PropNN
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_25_hgap3 (a b d e0p bImg : Point) (AB : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab : a ≠ b)
    (h1 : ∠ a:b:d = ∠ bImg:a:e0p) (h2 : |(b─a)| = |(a─bImg)|)
    (h3 : bImg.onLine AB) (h4 : ¬between bImg a b)
    (h5 : e0p.sameSide d AB) (h6 : a ≠ e0p) :
    e0p ≠ a ∧ ∠ e0p:a:b = ∠ a:b:d ∧ e0p.sameSide d AB := by
  have hbb : bImg = b := by
    by_contra hne
    euclid_apply (between_points a bImg b AB)
    euclid_finish
  subst hbb
  exact ⟨Ne.symm h6, by euclid_finish, h5⟩

end Elements.Book3
