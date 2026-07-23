import SystemE
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book1.Prop47.Main

namespace Elements.Book2

open Elements.Book1

theorem helper_14_geomean : ∀ (b e f : Point) (BF : Line),
  distinctPointsOnLine b f BF ∧ between b e f →
  ∃ (h : Point), |(e─h)| * |(e─h)| = |(b─e)| * |(e─f)| :=
by
  euclid_intros
  euclid_apply (proposition_10 b f BF) as g
  euclid_apply (circle_from_points g b) as α
  euclid_apply (point_on_circle_if g b f α)
  euclid_apply (circle_points_between b f e α)
  euclid_apply (proposition_11 b f e BF) as f0
  euclid_apply (line_from_points e f0) as EH
  euclid_apply (intersection_circle_line_2 e α EH)
  euclid_apply (intersections_circle_line α EH) as (h, h')
  euclid_apply (point_on_circle_onlyif g b h α)
  use h
  euclid_apply (line_from_points g h) as GH
  by_cases (e = g)
  · euclid_finish
  · have hperp : (∠ g:e:h : ℝ) = ∟ := by euclid_finish
    euclid_apply (proposition_47 e g h BF GH EH)
    euclid_finish

end Elements.Book2
