import SystemE

namespace Elements.Book1

theorem helper_1_47_step20 (a b c f g h k : Point) (GF AB AG BF HK AC AH CK : Line)
    (hpara_AB : formParallelogram g f a b GF AB AG BF)
    (hang_AB : ∠ b:a:g = ∟)
    (hag : |(a─g)| = |(a─b)|) (hgf : |(g─f)| = |(a─b)|)
    (hpara_AC : formParallelogram h k a c HK AC AH CK)
    (hang_AC : ∠ c:a:h = ∟)
    (hah : |(a─h)| = |(a─c)|) (hhk : |(h─k)| = |(a─c)|) :
    (Triangle.area △ a:g:f + Triangle.area △ a:f:b = |(b─a)| * |(b─a)|) ∧
      (Triangle.area △ a:h:k + Triangle.area △ a:k:c = |(a─c)| * |(a─c)|) := by
  euclid_finish

end Elements.Book1
