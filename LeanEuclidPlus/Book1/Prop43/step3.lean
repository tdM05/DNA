import SystemE
import Book1.Prop34.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_43_step3
  (a c f g k : Point) (EF BC GH CD AC : Line)
  (hkef : k.onLine EF) (hfef : f.onLine EF)
  (hgbc : g.onLine BC) (hcbc : c.onLine BC)
  (hkgh : k.onLine GH) (hggh : g.onLine GH)
  (hfcd : f.onLine CD) (hccd : c.onLine CD)
  (hpar1 : ¬EF.intersectsLine BC) (hpar2 : ¬GH.intersectsLine CD)
  (hss : k.sameSide g CD) (hfc : f ≠ c)
  (hkac : k.onLine AC) (hcac : c.onLine AC) (hac : a ≠ c)
  : Triangle.area △ k:f:c = Triangle.area △ k:g:c := by
  euclid_apply (proposition_34 f c k g CD GH EF BC AC)
  euclid_finish

end Elements.Book1
