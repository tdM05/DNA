import SystemE
import Book1.Prop36.step1
import Book1.Prop36.step2
import Book1.Prop36.step3
import Book1.Prop36.step4
import Book1.Prop36.step5
import Book1.Prop36.step6
import Book1.Prop36.step7
import Book1.Prop36.step8
import Book1.Prop36.step9
import Book1.Prop36.step2_assumption2
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem proposition_36 : ∀ (a b c d e f g h : Point) (AH BG AB CD EF HG : Line),
  formParallelogram a d b c AH BG AB CD ∧ formParallelogram e h f g AH BG EF HG ∧
  |(b─c)| = |(f─g)| ∧ (between a d h) ∧ (between a e h) →
  Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by
  euclid_intros

  euclid_apply (line_from_points b e) as BE
  euclid_apply (line_from_points c h) as CH
  have s1 : distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH := by euclid_apply (h_1_36_s1 b c e f g h AH BG HG BE CH (by (show b.onLine BG; assumption)) (by (show c.onLine BG; assumption)) (by (show e.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show h.onLine HG; assumption)) (by (show g.onLine HG; assumption)) (by (show h ≠ g; assumption)) (by (show e.sameSide f HG; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)))

  have s2_a1 : |(b─c)| = |(f─g)| := by assumption

  have s2_a2 : |(f─g)| = |(e─h)| := by euclid_apply (h_1_36_s2_x1 e f g h AH BG EF HG (by (show e.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show h.onLine HG; assumption)) (by (show g.onLine HG; assumption)) (by (show h ≠ g; assumption)) (by (show e.sameSide f HG; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬EF.intersectsLine HG; assumption)))

  have s2 : |(b─c)| = |(e─h)| := by euclid_apply (h_1_36_s2 e f g h AH BG EF HG (by (show e.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show h.onLine HG; assumption)) (by (show g.onLine HG; assumption)) (by (show h ≠ g; assumption)) (by (show e.sameSide f HG; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬EF.intersectsLine HG; assumption)) (by (show |(b─c)| = |(f─g)|; assumption)) (by (show |(f─g)| = |(e─h)|; assumption)))

  have s3 : ¬(BG.intersectsLine AH) := by euclid_apply (h_1_36_s3 AH BG (by (show ¬AH.intersectsLine BG; assumption)))

  have s4 : distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH := by euclid_apply (h_1_36_s4 b c e h BE CH (by (show distinctPointsOnLine b e BE ∧ distinctPointsOnLine c h CH; assumption)))

  have s5 : |(e─b)| = |(h─c)| ∧ ¬(BE.intersectsLine CH) := by euclid_apply (h_1_36_s5 a b c d e h AH BG AB CD BE CH (by (show a.onLine AH; assumption)) (by (show e.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show b.onLine BG; assumption)) (by (show c.onLine BG; assumption)) (by (show d.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show |(b─c)| = |(e─h)|; assumption)) (by (show distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH; assumption)) (by (show between a e h; assumption)) (by (show between a d h; assumption)))

  have s6 : formParallelogram e h b c AH BG BE CH := by euclid_apply (h_1_36_s6 a b c d e h AH BG AB CD BE CH (by (show a.onLine AH; assumption)) (by (show e.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show b.onLine BG; assumption)) (by (show c.onLine BG; assumption)) (by (show d.onLine AH; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH; assumption)) (by (show |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH; assumption)) (by (show between a e h; assumption)) (by (show between a d h; assumption)))

  have s7_a1 : distinctPointsOnLine b c BG := by euclid_finish

  have s7_a2 : ¬(BG.intersectsLine AH) := by assumption

  have s7 : Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by euclid_apply (h_1_36_s7 a b c d e h AH BG AB CD BE CH (by (show a.onLine AH; assumption)) (by (show d.onLine AH; assumption)) (by (show b.onLine BG; assumption)) (by (show c.onLine BG; assumption)) (by (show a.onLine AB; assumption)) (by (show b.onLine AB; assumption)) (by (show d.onLine CD; assumption)) (by (show c.onLine CD; assumption)) (by (show d ≠ c; assumption)) (by (show a.sameSide b CD; assumption)) (by (show ¬AB.intersectsLine CD; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show formParallelogram e h b c AH BG BE CH; assumption)) (by (show distinctPointsOnLine b c BG; assumption)) (by (show ¬(BG.intersectsLine AH); assumption)))

  have s8 : Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by euclid_apply (h_1_36_s8 b c e f g h AH BG EF HG BE CH (by (show e.onLine AH; assumption)) (by (show h.onLine AH; assumption)) (by (show b.onLine BG; assumption)) (by (show c.onLine BG; assumption)) (by (show f.onLine BG; assumption)) (by (show g.onLine BG; assumption)) (by (show e.onLine EF; assumption)) (by (show f.onLine EF; assumption)) (by (show h.onLine HG; assumption)) (by (show g.onLine HG; assumption)) (by (show h ≠ g; assumption)) (by (show e.sameSide f HG; assumption)) (by (show ¬AH.intersectsLine BG; assumption)) (by (show ¬EF.intersectsLine HG; assumption)) (by (show b.onLine BE; assumption)) (by (show e.onLine BE; assumption)) (by (show c.onLine CH; assumption)) (by (show h.onLine CH; assumption)) (by (show distinctPointsOnLine e b BE ∧ distinctPointsOnLine h c CH; assumption)) (by (show |(e─b)| = |(h─c)| ∧ ¬BE.intersectsLine CH; assumption)) (by (show formParallelogram e h b c AH BG BE CH; assumption)))

  have s9 : Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:f:h + Triangle.area △ h:f:g := by euclid_apply (h_1_36_s9 a b c d e f g h (by (show Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c; assumption)) (by (show Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h; assumption)))

  exact s9

end Elements.Book1
