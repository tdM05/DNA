import SystemE

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB CH : Line)
    (ha : a.onLine AB) (hb : b.onLine AB) (hab : a ≠ b)
    (hh : h.onLine AB) (he : e.onLine AB) (hg : g.onLine AB)
    (hehg : between e h g) (hc : ¬(c.onLine AB))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH)
    (hr : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  by_cases hah : a = h
  · right
    by_cases hbp : between e h b
    · euclid_apply (equal_angles h g b c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e b c c AB CH)
      euclid_finish
  · left
    by_cases hap : between e h a
    · euclid_apply (equal_angles h g a c c AB CH)
      euclid_finish
    · euclid_apply (equal_angles h e a c c AB CH)
      euclid_finish

end Elements.Book1
