import SystemE
import Helpers.SameSide
import Book1.Prop45.step17_fkne

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step20 (f g h k l m : Point) (FG KH FK GH HM LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a5 : f.onLine FK) (a6 : k.onLine FK)
    (a7 : g.onLine GH) (a8 : h.onLine GH) (a9 : g ≠ h)
    (a10 : f.sameSide k GH)
    (a11 : ¬FG.intersectsLine KH) (a12 : ¬FK.intersectsLine GH)
    (b2 : m.onLine HM) (b7 : m.onLine LM) (b8 : l.onLine LM) (b9 : m ≠ l)
    (c1 : ¬k.onLine GH) (c2 : ¬m.onLine GH) (c3 : ¬m.sameSide k GH)
    (hstep10 : KH = HM)
    (hstep17 : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM))
    (hstep18 : distinctPointsOnLine k m KH ∧ distinctPointsOnLine f l FG)
    : formParallelogram f l k m FG KH FK LM := by
  have step17_fkne : FK ≠ LM := by euclid_apply (helper_1_45_step17_fkne f g h k l m FG KH FK GH HM LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.sameSide k GH; assumption)) (by euclid_assumption "" (show KH = HM; assumption)))
  have hfk_ss : f.sameSide k LM :=
    sameSide_of_parallel_both f k FK LM a5 a6 step17_fkne hstep17.2
  exact ⟨a1, hstep18.2.2.1, a3, hstep18.1.2.1, a5, a6,
    ⟨b8, b7, b9.symm⟩, hfk_ss, a11, hstep17.2⟩

end Elements.Book1
