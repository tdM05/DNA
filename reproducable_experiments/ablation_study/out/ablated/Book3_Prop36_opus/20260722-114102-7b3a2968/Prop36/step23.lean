import SystemE
import Book1.Prop47.Main

namespace Elements.Book3

theorem helper_3_36_step23 (a c d e f : Point) (ABC : Circle) (DA EF EC : Line)
    (h1 : ∠ e:f:c = ∟)
    (h2 : e.isCentre ABC ∧ e.onLine EF ∧ ¬e.onLine DA ∧ (∠ a:f:e = ∟ ∨ ∠ c:f:e = ∟))
    (h3 : c.onCircle ABC)
    (h4 : f.onLine EF) (h5 : f.onLine DA)
    (h6 : a.onLine DA) (h7 : d.onLine DA) (h8 : between d c a)
    (h9 : e.onLine EC) (h10 : c.onLine EC) :
    |(e─c)| * |(e─c)| = |(f─c)| * |(f─c)| + |(e─f)| * |(e─f)| := by
  obtain ⟨he, heEF, henDA, _⟩ := h2
  euclid_apply (Elements.Book1.proposition_47 f e c EF EC DA)
  euclid_finish

end Elements.Book3
