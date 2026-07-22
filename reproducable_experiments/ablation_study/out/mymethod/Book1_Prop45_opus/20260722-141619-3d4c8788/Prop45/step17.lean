import SystemE
import Book1.Prop30.Main
import Book1.Prop45.step17_assumption1
import Book1.Prop45.step17_assumption2
import Book1.Prop45.step17_fkne

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17 (f g h k l m : Point) (FG KH FK GH HM GL LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a5 : f.onLine FK) (a6 : k.onLine FK)
    (a7 : g.onLine GH) (a8 : h.onLine GH) (a9 : g ≠ h)
    (a10 : f.sameSide k GH)
    (a11 : ¬FG.intersectsLine KH) (a12 : ¬FK.intersectsLine GH)
    (b1 : h.onLine HM) (b2 : m.onLine HM)
    (b3 : g.onLine GL) (b4 : l.onLine GL)
    (b7 : m.onLine LM) (b8 : l.onLine LM) (b9 : m ≠ l)
    (b10 : h.sameSide g LM)
    (b11 : ¬HM.intersectsLine GL) (b12 : ¬GH.intersectsLine LM)
    (c1 : ¬k.onLine GH) (c2 : ¬m.onLine GH) (c3 : ¬m.sameSide k GH)
    (hstep10 : KH = HM) (hstep16 : FG = GL)
    (hstep17_assumption1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH))
    (hstep17_assumption2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM))
    : |(k─f)| = |(m─l)| ∧ ¬(FK.intersectsLine LM) := by
  -- The sentence applies [Prop.~1.34] to the two constructed parallelograms to get the
  -- equal-and-parallel facts, then [Prop.~1.30] (parallel-transitivity) for the conclusion.
  have step17_assumption1 : |(f─k)| = |(h─g)| ∧ ¬(FK.intersectsLine GH) := by euclid_apply (helper_1_45_step17_assumption1 f g h k FG KH FK GH (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)))
  have step17_assumption2 : |(h─g)| = |(m─l)| ∧ ¬(GH.intersectsLine LM) := by euclid_apply (helper_1_45_step17_assumption2 g h l m HM GL GH LM (by euclid_assumption "" (show h.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show g.onLine GL; assumption)) (by euclid_assumption "" (show l.onLine GL; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show m ≠ l; assumption)) (by euclid_assumption "" (show h.sameSide g LM; assumption)) (by euclid_assumption "" (show ¬HM.intersectsLine GL; assumption)) (by euclid_assumption "" (show ¬GH.intersectsLine LM; assumption)))
  euclid_apply (parallelogram_same_side f g k h FG KH FK GH)
  euclid_apply (parallelogram_same_side h m g l HM GL GH LM)
  have step17_fkne : FK ≠ LM := by euclid_apply (helper_1_45_step17_fkne f g h k l m FG KH FK GH HM LM (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine KH; assumption)) (by euclid_assumption "" (show h.onLine KH; assumption)) (by euclid_assumption "" (show f.onLine FK; assumption)) (by euclid_assumption "" (show k.onLine FK; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show f.sameSide k GH; assumption)) (by euclid_assumption "" (show ¬FG.intersectsLine KH; assumption)) (by euclid_assumption "" (show ¬FK.intersectsLine GH; assumption)) (by euclid_assumption "" (show m.onLine HM; assumption)) (by euclid_assumption "" (show m.onLine LM; assumption)) (by euclid_assumption "" (show l.onLine LM; assumption)) (by euclid_assumption "" (show ¬k.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.onLine GH; assumption)) (by euclid_assumption "" (show ¬m.sameSide k GH; assumption)) (by euclid_assumption "" (show KH = HM; assumption)))
  euclid_apply (proposition_30 FK LM GH)
  euclid_finish

end Elements.Book1
