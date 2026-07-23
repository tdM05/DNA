import SystemE

namespace Elements.Book3

theorem helper_3_36_step1 (ABC : Circle) (DA : Line) :
    (∃ f : Point, f.isCentre ABC ∧ f.onLine DA) ∨
    ¬(∃ f : Point, f.isCentre ABC ∧ f.onLine DA) :=
  Classical.em _

end Elements.Book3
