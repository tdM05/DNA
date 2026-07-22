import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_fkne (f g h k l m : Point) (FG KH FK GH HM LM : Line)
    (a1 : f.onLine FG) (a2 : g.onLine FG)
    (a3 : k.onLine KH) (a4 : h.onLine KH)
    (a5 : f.onLine FK) (a6 : k.onLine FK)
    (a7 : g.onLine GH) (a8 : h.onLine GH) (a9 : g ≠ h)
    (a10 : f.sameSide k GH)
    (a11 : ¬FG.intersectsLine KH) (a12 : ¬FK.intersectsLine GH)
    (b2 : m.onLine HM) (b7 : m.onLine LM) (b8 : l.onLine LM)
    (hk : ¬k.onLine GH) (hm : ¬m.onLine GH) (hkm : ¬m.sameSide k GH)
    (hstep10 : KH = HM)
    : FK ≠ LM := by
  euclid_apply (parallelogram_same_side f g k h FG KH FK GH)
  euclid_finish

end Elements.Book1
