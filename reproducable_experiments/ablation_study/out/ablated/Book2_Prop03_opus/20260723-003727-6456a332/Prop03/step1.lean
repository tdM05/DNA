import SystemE

namespace Elements.Book2

theorem helper_2_3_step1 (b c d e : Point)
    (h1 : |(c─d)| = |(c─b)|) (h2 : |(b─e)| = |(c─b)|) (h3 : |(d─e)| = |(c─b)|)
    (h4 : ∠ b:c:d = ∟) (h5 : ∠ c:d:e = ∟) (h6 : ∠ c:b:e = ∟) (h7 : ∠ b:e:d = ∟) :
    |(c─d)| = |(c─b)| ∧ |(b─e)| = |(c─b)| ∧ |(d─e)| = |(c─b)| ∧
      (∠ b:c:d = ∟) ∧ (∠ c:d:e = ∟) ∧ (∠ c:b:e = ∟) ∧ (∠ b:e:d = ∟) := by
  euclid_finish

end Elements.Book2
