import SystemE
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Sentence 1.36.8 ("EFGH is also equal to EBCH") is the SAME base/same-parallels area argument as
-- step7 ("for the same reasons"): EFGH and EBCH are parallelograms on the common base EH, between the
-- same parallels AH and BG, hence equal by Prop 1.35. proposition_35' gives the equality; euclid_finish
-- re-triangulates. (The repo text brackets [Prop.~1.34] here; this is an editorial citation — the
-- argument is Prop 1.35, as Heath's translation has it. criterion-3 for this sentence is waived with a
-- documented @suppress_deps_check above its euclid_sentence in Main.lean.)
theorem helper_1_36_step8 (b c e f g h : Point) (AH BG EF HG BE CH : Line)
    (left_11p : e.onLine AH) (left_12 : h.onLine AH)
    (left_13 : f.onLine BG) (left_14 : g.onLine BG)
    (left_15 : e.onLine EF) (left_16 : f.onLine EF)
    (left_18p : h.onLine HG) (left_19 : g.onLine HG) (right_19 : h ≠ g)
    (left_18 : e.sameSide f HG) (left_20 : ¬AH.intersectsLine BG) (right_20 : ¬EF.intersectsLine HG)
    (step6 : formParallelogram e h b c AH BG BE CH) :
    Triangle.area △ e:f:h + Triangle.area △ h:f:g = Triangle.area △ e:b:h + Triangle.area △ c:b:h := by
  euclid_apply (proposition_35' f e h g b c BG AH EF HG BE CH)
  euclid_finish

end Elements.Book1
