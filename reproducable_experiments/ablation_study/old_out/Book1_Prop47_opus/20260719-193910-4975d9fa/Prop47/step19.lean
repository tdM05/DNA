import SystemE

namespace Elements.Book1

theorem helper_1_47_step19 (b c d e : Point) (DE BC BD CE : Line)
    (hpara : formParallelogram d e b c DE BC BD CE)
    (hang : ∠ c:b:d = ∟)
    (hbd : |(b─d)| = |(b─c)|) (hde : |(d─e)| = |(b─c)|) :
    Triangle.area △ b:d:e + Triangle.area △ b:e:c = |(b─c)| * |(b─c)| := by
  euclid_finish

end Elements.Book1
