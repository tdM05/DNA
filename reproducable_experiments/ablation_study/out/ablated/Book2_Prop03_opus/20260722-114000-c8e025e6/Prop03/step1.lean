import SystemE

namespace Elements.Book2

theorem helper_2_3_step1 (b c d e : Point)
    (hcd : |(c─d)| = |(c─b)|) (hbe : |(b─e)| = |(c─b)|) (hde : |(d─e)| = |(c─b)|)
    (hbcd : ∠ b:c:d = ∟) (hcde : ∠ c:d:e = ∟) (hcbe : ∠ c:b:e = ∟) (hbed : ∠ b:e:d = ∟) :
    |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧
      (∠ b:c:d = ∟) ∧ (∠ c:d:e = ∟) ∧ (∠ c:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  exact ⟨hcd, hbe, hde, hbcd, hcde, hcbe, hbed⟩

end Elements.Book2
