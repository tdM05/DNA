import SystemE
import Book1.Prop03.Main
import Book2Unfaithful.Helper14_geomean

namespace Elements.Book2

open Elements.Book1

theorem helper_14_product : ∀ (f g e : Point) (FG FE : Line),
  distinctPointsOnLine f g FG ∧ distinctPointsOnLine f e FE →
  ∃ (h : Point), |(g─h)| * |(g─h)| = |(f─g)| * |(f─e)| :=
by
  euclid_intros
  euclid_apply (extend_point_longer FG f g (f─e)) as x
  euclid_apply (proposition_3 g x f e FG FE) as f0
  have hbet : between f g f0 := by euclid_finish
  euclid_apply (helper_14_geomean f g f0 FG) as hh
  use hh
  euclid_finish

end Elements.Book2
