import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

theorem helper_3_36_step24 (a c d e f : Point) (ABC : Circle) (DA EF ED : Line)
    (h1 : ∠ e:f:c = ∟)
    (h2 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    (h3 : e.onLine EF) (h4 : f.onLine EF)
    (h5 : a.onLine DA) (h6 : d.onLine DA) (h7 : f.onLine DA) (h8 : between d c a)
    (h9 : e.onLine ED) (h10 : d.onLine ED) :
    |(e─d)| * |(e─d)| = |(d─f)| * |(d─f)| + |(f─e)| * |(f─e)| := by
  obtain ⟨he, heEF, henDA, _⟩ := h2
  have hperp : ∠ e:f:d = ∟ := by euclid_finish
  euclid_apply (Elements.Book1.proposition_47 f e d EF ED DA)
  euclid_finish

end Elements.Book3
