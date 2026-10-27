import SystemE
import Book1Variants.Prop35
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

-- Sentence 1.36.7 cites [Prop.~1.35]: EBCH and ABCD are parallelograms on the same base BC and
-- between the same parallels AH, BG, so they are equal (Prop 1.35). proposition_35' (general
-- position) gives the area equality; euclid_finish re-triangulates EBCH to the claimed form.
theorem helper_1_36_step7 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
    (left_1 : a.onLine AH) (left_2 : d.onLine AH)
    (left_3 : b.onLine BG) (left_4 : c.onLine BG)
    (left_5 : a.onLine AB) (left_6 : b.onLine AB)
    (left_8p : d.onLine CD) (left_9 : c.onLine CD) (right_9 : d ≠ c)
    (left_8 : a.sameSide b CD) (left_10 : ¬AH.intersectsLine BG) (right_10 : ¬AB.intersectsLine CD)
    (step6 : formParallelogram e h b c AH BG BE CH)
    -- Reasoning hypotheses (from @assumption — keep these types in the signature):
    (hassump1 : distinctPointsOnLine b c BG)   -- "$BC$, as ($ABCD$)"
    (hassump2 : ¬(BG.intersectsLine AH))   -- "$BC$ and $AH$, as ($ABCD$) [Prop.~1.35]"
    : Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_finish

end Elements.Book1
