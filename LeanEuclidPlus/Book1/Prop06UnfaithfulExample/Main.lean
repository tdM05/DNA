import SystemE

namespace Elements.Book1

theorem proposition_6 : ∀ (a b c : Point) (AB BC AC : Line),
  formTriangle a b c AB BC AC ∧ (∠ a:b:c = ∠ a:c:b) →
  |(a─b)| = |(a─c)| := by
  euclid_intros
  euclid_apply (superposition a b c a c b AB BC AC AC) as (b', c', BC', AC')
  euclid_finish

end Elements.Book1
