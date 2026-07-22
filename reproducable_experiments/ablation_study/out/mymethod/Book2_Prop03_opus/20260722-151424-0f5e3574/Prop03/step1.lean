import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

theorem helper_2_3_step1 (b c d e : Point) (CD BE DE : Line)
    (h_cd : |(c─d)| = |(c─b)|) (h_be : |(b─e)| = |(c─b)|) (h_de : |(d─e)| = |(c─b)|)
    (h_bcd : ∠ b:c:d = ∟) (h_cde : ∠ c:d:e = ∟) (h_cbe : ∠ c:b:e = ∟) (h_bed : ∠ b:e:d = ∟) :
    |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧
      (∠ b:c:d = ∟) ∧ (∠ c:d:e = ∟) ∧ (∠ c:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  exact ⟨h_cd, h_be, h_de, h_bcd, h_cde, h_cbe, h_bed⟩

end Elements.Book2
