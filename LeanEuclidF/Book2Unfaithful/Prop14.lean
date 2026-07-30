import SystemE
import Book1.Prop11.Main
import Book1.Prop42.Main
import Book1.Prop45.Main
import Book1Variants.Prop11
import Book2Unfaithful.Helper14_product

namespace Elements.Book2

open Elements.Book1

theorem proposition_14 : ∀ (a b c : Point) (AB BC CA : Line),
  formTriangle a b c AB BC CA →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:c :=
by
  euclid_intros
  euclid_apply (proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  euclid_apply (proposition_42 a b c p a b AB BC CA AP AB) as (f, g, e2, c', FG, EC, EF, CG)
  euclid_apply (rectangle_area f g e2 c' FG EC EF CG)
  euclid_apply (helper_14_product f g e2 FG EF) as hh
  use g, hh
  euclid_finish

theorem proposition_14' : ∀ (a b c d : Point) (AB BC CD AD DB : Line),
  formTriangle a b d AB DB AD ∧ formTriangle b c d BC CD DB ∧ a.opposingSides c DB →
  ∃ (e h : Point),
    |(e─h)| * |(e─h)| = Triangle.area △ a:b:d + Triangle.area △ d:b:c :=
by
  euclid_intros
  euclid_apply (proposition_11'' a b AB) as p
  euclid_apply (line_from_points a p) as AP
  euclid_apply (proposition_45 a b c d p a b AB BC CD AD DB AP AB) as (f, l, k, m, FL, KM, FK, LM)
  euclid_apply (rectangle_area f l k m FL KM FK LM)
  euclid_apply (helper_14_product f l k FL FK) as hh
  use l, hh
  euclid_finish

end Elements.Book2
