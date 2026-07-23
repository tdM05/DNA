import SystemE
import Book1.Prop03.Main
import Book1.Prop10.Main
import Book1.Prop11.Main
import Book1.Prop47.Main
import Book1Variants.Prop11
import Book2Unfaithful.Helper11_golden

namespace Elements.Book2

open Elements.Book1

theorem proposition_11 : ∀ (a b : Point) (AB : Line),
  distinctPointsOnLine a b AB →
  ∃ h : Point, between a h b ∧
    |(a─b)| * |(b─h)| = |(a─h)| * |(a─h)| :=
by
  euclid_intros
  euclid_apply (proposition_10 a b AB) as m
  euclid_apply (proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  euclid_apply (extend_point_longer AP a p (a─m)) as e0
  euclid_apply (proposition_3 a e0 a m AP AB) as e
  have h_angle : ∠ e:a:b = ∟ := by euclid_finish
  euclid_apply (line_from_points e b) as EB
  euclid_apply (proposition_47 a e b AP EB AB)
  have hA  : |(a─b)| = |(a─m)| + |(a─m)| := by euclid_finish
  have hE  : |(a─e)| = |(a─m)| := by euclid_finish
  have hpy : |(e─b)| * |(e─b)| = |(a─e)| * |(a─e)| + |(a─b)| * |(a─b)| := by euclid_finish
  euclid_apply (extend_point_longer AP e a (e─b)) as f0
  euclid_apply (proposition_3 e f0 e b AP EB) as f
  have hQ : |(e─b)| = |(a─e)| + |(a─f)| := by euclid_finish
  have hMpos : |(a─m)| > 0 := by euclid_finish
  have hEBnn : |(e─b)| ≥ 0 := by euclid_finish
  have hlt : |(a─f)| < |(a─b)| :=
    helper_11_af_lt_ab |(a─b)| |(a─m)| |(a─e)| |(e─b)| |(a─f)| hMpos hA hE hpy hQ hEBnn
  euclid_apply (proposition_3 a b a f AB AP) as h
  use h
  have hAH : |(a─h)| = |(a─f)| := by euclid_finish
  have hBH : |(a─b)| = |(a─h)| + |(b─h)| := by euclid_finish
  refine ⟨by euclid_finish, ?_⟩
  exact helper_11_golden |(a─b)| |(a─m)| |(a─e)| |(e─b)| |(a─f)| |(a─h)| |(b─h)|
    hA hE hpy hQ hAH hBH

end Elements.Book2
