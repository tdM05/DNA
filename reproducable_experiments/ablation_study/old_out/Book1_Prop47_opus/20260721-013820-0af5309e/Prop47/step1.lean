import SystemE

namespace Elements.Book1

theorem helper_1_47_step1 (a b c d e f g h k : Point)
    (h1 : |(b─d)| = |(b─c)|) (h2 : |(c─e)| = |(b─c)|) (h3 : |(d─e)| = |(b─c)|)
    (h4 : ∠ c:b:d = ∟) (h5 : ∠ b:d:e = ∟) (h6 : ∠ b:c:e = ∟) (h7 : ∠ c:e:d = ∟)
    (h8 : |(a─g)| = |(a─b)|) (h9 : |(b─f)| = |(a─b)|) (h10 : |(g─f)| = |(a─b)|)
    (h11 : ∠ b:a:g = ∟) (h12 : ∠ a:g:f = ∟) (h13 : ∠ a:b:f = ∟) (h14 : ∠ b:f:g = ∟)
    (h15 : |(a─h)| = |(a─c)|) (h16 : |(c─k)| = |(a─c)|) (h17 : |(h─k)| = |(a─c)|)
    (h18 : ∠ c:a:h = ∟) (h19 : ∠ a:h:k = ∟) (h20 : ∠ a:c:k = ∟) (h21 : ∠ c:k:h = ∟) :
    (|(b─d)| = |(b─c)| ∧ |(c─e)| = |(b─c)| ∧ |(d─e)| = |(b─c)| ∧
      (∠ c:b:d = ∟) ∧ (∠ b:d:e = ∟) ∧ (∠ b:c:e = ∟) ∧ (∠ c:e:d = ∟)) ∧
    (|(a─g)| = |(a─b)| ∧ |(b─f)| = |(a─b)| ∧ |(g─f)| = |(a─b)| ∧
      (∠ b:a:g = ∟) ∧ (∠ a:g:f = ∟) ∧ (∠ a:b:f = ∟) ∧ (∠ b:f:g = ∟)) ∧
    (|(a─h)| = |(a─c)| ∧ |(c─k)| = |(a─c)| ∧ |(h─k)| = |(a─c)| ∧
      (∠ c:a:h = ∟) ∧ (∠ a:h:k = ∟) ∧ (∠ a:c:k = ∟) ∧ (∠ c:k:h = ∟)) := by
  euclid_finish

end Elements.Book1
