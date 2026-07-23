import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_36_step8
  (b d f : Point) (ABC : Circle) (DB FB : Line)
  (hf_FB : f.onLine FB) (hb_FB : b.onLine FB) (hb_DB : b.onLine DB) (hd_DB : d.onLine DB)
  (hb_circ : b.onCircle ABC) (hfcenter : f.isCentre ABC) (hnint : ¬ DB.intersectsCircle ABC)
  (hd_out : ¬ d.insideCircle ABC) (hd_noncirc : ¬ d.onCircle ABC)
  (hstep3 : ∠ f:b:d = ∟)
  : |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  have hd_notFB : ¬ d.onLine FB := by
    intro hdFB
    euclid_apply (between_points f b d FB)
    euclid_finish
  euclid_apply (line_from_points f d) as FD
  have hne : FB ≠ FD := by
    intro heq
    rw [heq] at hd_notFB
    euclid_finish
  euclid_apply (Elements.Book1.proposition_47 b f d FB FD DB)
  euclid_finish

end Elements.Book3
