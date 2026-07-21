import SystemE

namespace Elements.Book1

theorem helper_1_12_step11 (a b c e g h : Point) (AB CH : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : e.onLine AB) (h5 : g.onLine AB) (h6 : h.onLine AB)
    (h7 : h.onLine CH) (h8 : c.onLine CH) (h9 : ¬(c.onLine AB))
    (h10 : between e h g)
    (h11 : ∠ c:h:g = ∟ ∧ ∠ e:h:c = ∟) :
    ∠ a:h:c = ∟ ∨ ∠ b:h:c = ∟ := by
  obtain ⟨hr1, hr2⟩ := h11
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
