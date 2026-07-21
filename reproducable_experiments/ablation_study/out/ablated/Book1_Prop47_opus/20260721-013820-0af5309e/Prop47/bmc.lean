import SystemE
import Book1Variants.Prop29
import Book1.Prop16.Main
import Book1.Prop17.Main

namespace Elements.Book1

-- The altitude foot m = AL ∩ BC (AL ∥ BD ⊥ BC) lies between b and c, since ∠bac = ∟.
theorem helper_1_47_bmc (a b c d m : Point) (AB BC AC BD AL : Line)
    (h1 : a.onLine AB) (h2 : b.onLine AB) (h3 : a ≠ b)
    (h4 : b.onLine BC) (h5 : c.onLine BC) (h6 : b ≠ c)
    (h7 : c.onLine AC) (h8 : a.onLine AC) (h6b : a ≠ c)
    (h9 : b.onLine BD) (h10 : d.onLine BD)
    (h11 : ∠ c:b:d = ∟) (h12 : ∠ b:a:c = ∟)
    (h13 : ¬(a.onLine BC)) (h14 : ¬(d.onLine BC)) (h15 : ¬(d.sameSide a BC))
    (h16 : a.onLine AL) (h17 : m.onLine AL) (h18 : m.onLine BC)
    (h19 : ¬(AL.intersectsLine BD)) (h20 : ¬(a.onLine BD)) (h21 : a ≠ m)
    (h22 : b ≠ m) (h23 : c ≠ m)
    (h24 : AB ≠ BC) (h25 : BC ≠ AC) (h26 : AC ≠ AB) :
    between b m c := by
  euclid_apply (extend_point BD d b) as d'
  euclid_apply (proposition_29''''' a d' m b AL BD BC)
  have hamb : ∠ a:m:b = ∟ := by euclid_finish
  have hamc : ∠ a:m:c = ∟ := by euclid_finish
  euclid_apply (line_from_points a m) as AM
  have htri := between_points b m c BC (by euclid_finish)
  rcases htri with h | h | h
  · exact h
  · exfalso
    euclid_apply (proposition_16 a c b m AC BC AB)
    euclid_apply (proposition_17 a b m AB BC AM)
    euclid_finish
  · exfalso
    euclid_apply (proposition_16 a b c m AB BC AC)
    euclid_apply (proposition_17 a c m AC BC AM)
    euclid_finish

end Elements.Book1
