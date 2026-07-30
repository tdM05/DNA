import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem h_1_22_s12
    (g h k : Point) (KLH : Circle)
    (hassump1 : g.isCentre KLH)
    (hhOnKLH : h.onCircle KLH)
    (hkOnKLH : k.onCircle KLH) :
    |(g─h)| = |(g─k)| :=
  point_on_circle_onlyif g k h KLH ⟨hassump1, hkOnKLH, hhOnKLH⟩

end Elements.Book1
