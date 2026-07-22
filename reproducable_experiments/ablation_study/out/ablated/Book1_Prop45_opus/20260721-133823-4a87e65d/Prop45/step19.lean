import SystemE
import Book1.Prop33.Main

namespace Elements.Book1

theorem helper_1_45_step19 (e₁ e₂ e₃ f h k l m : Point) (FK LM KH FG : Line)
    (h1 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (h2 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    (h3 : k.onLine FK) (h4 : f.onLine FK) (h5 : m.onLine LM) (h6 : l.onLine LM)
    (h7 : m ≠ l) (h8 : ∠ h:k:f = ∠ e₁:e₂:e₃) (h9 : ∠ e₁:e₂:e₃ > 0)
    (h10 : ¬(FG.intersectsLine KH)) :
    |(k─m)| = |(f─l)| ∧ ¬(KH.intersectsLine FG) := by
  euclid_apply (proposition_33 k f m l FK LM KH FG)
  euclid_finish

end Elements.Book1
