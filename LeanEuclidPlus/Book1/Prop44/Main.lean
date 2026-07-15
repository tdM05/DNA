import SystemE
import Book1Variants.Prop29
import Book1.Prop31.Main
import Book1Variants.Prop42
import Book1.Prop43.Main

namespace Elements.Book1

theorem proposition_44 : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) := by
  euclid_intros
  euclid_intro_sentence "1.44.0"
    "To apply a parallelogram equal to a given triangle to a given straight-line in a given rectilinear angle. Let $AB$ be the given straight-line,  $C$ the given triangle, and $D$ the given rectilinear angle. So it is required to apply a parallelogram equal to the given triangle $C$ to the given straight-line $AB$ in an angle equal to (angle) $D$. "

  -- f = Euclid's G, g = Euclid's F, e = Euclid's E
  -- GF = line through G,F; BG = line through B,G; EF = line through E,F
  euclid_apply (proposition_42'' c₁ c₂ c₃ d₁ d₂ d₃ a b C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (f, g, e, GF, BG, EF)
  euclid_sentence "1.44.1"
    "Let the parallelogram $BEFG$, equal to the triangle $C$, have been constructed in the angle $EBG$, which is equal to $D$ [Prop.~1.42]."
    (step1 : formParallelogram f g b e GF AB BG EF ∧ ∠ e:b:f = ∠ d₁:d₂:d₃ ∧
      Triangle.area △ f:b:e + Triangle.area △ f:e:g = Triangle.area △ c₁:c₂:c₃) := by sorry

  euclid_sentence "1.44.2"
    "And let it have been placed so that $BE$ is straight-on to $AB$. "
    (step2 : between a b e) := by sorry

  -- Draw AH parallel to BG through a; h = intersection of AH with line GF
  euclid_apply (proposition_31 a b f BG) as AH
  euclid_apply (intersection_lines AH GF) as h
  euclid_sentence "1.44.3"
    "And let $FG$ have been drawn through to $H$,"
    (step3 : between g f h) := by sorry

  euclid_sentence "1.44.4"
    "and let $AH$ have been drawn through A parallel to either of $BG$ or $EF$ [Prop.~1.31],"
    (step4 : h.onLine AH ∧ ¬(AH.intersectsLine BG)) := by sorry

  euclid_apply (line_from_points h b) as HB
  euclid_sentence "1.44.5"
    "and let $HB$ have been joined."
    (step5 : distinctPointsOnLine h b HB) := by sorry

  -- @assumption_gap
  have step6_assumption1 : ¬(AH.intersectsLine EF) ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF := by sorry
  -- @assumption ("the straight-line $HF$ falls across the parallels $AH$ and $EF$", ¬(AH.intersectsLine EF) ∧ GF.intersectsLine AH ∧ GF.intersectsLine EF)
  euclid_sentence "1.44.6"
    "And since the straight-line $HF$ falls across the parallels $AH$ and $EF$, the (sum of the) angles $AHF$ and $HFE$ is thus equal to two right-angles [Prop.~1.29]."
    (step6 : ∠ a:h:g + ∠ h:g:e = ∟ + ∟) := by sorry

  euclid_sentence "1.44.7"
    "Thus, (the sum of) $BHG$ and $GFE$ is less than two right-angles."
    (step7 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟) := by sorry

  euclid_sentence "1.44.8"
    "And (straight-lines) produced to infinity from (internal angles whose sum is) less than two right-angles meet together [Post.~5]."
    (step8 : ∠ b:h:f + ∠ f:g:e < ∟ + ∟ → HB.intersectsLine EF) := by sorry

  euclid_sentence "1.44.9"
    "Thus, being produced, $HB$ and $FE$ will meet together."
    (step9 : HB.intersectsLine EF) := by sorry

  euclid_apply (intersection_lines HB EF) as k
  euclid_sentence "1.44.10"
    "Let them have been produced, and let them meet together at $K$."
    (step10 : k.onLine HB ∧ k.onLine EF) := by sorry

  euclid_apply (proposition_31 k a b AB) as KL
  euclid_sentence "1.44.11"
    "And let $KL$ have been drawn through point $K$ parallel to either of $EA$ or $FH$ [Prop.~1.31]."
    (step11 : k.onLine KL ∧ ¬(KL.intersectsLine AB)) := by sorry

  euclid_apply (intersection_lines KL AH) as l
  euclid_apply (intersection_lines KL BG) as m
  euclid_sentence "1.44.12"
    "And let $HA$ and $GB$ have been produced to points $L$ and $M$ (respectively)."
    (step12 : between h a l ∧ between f b m) := by sorry

  euclid_sentence "1.44.13"
    "Thus, $HLKF$ is a parallelogram,"
    (step13 : formParallelogram h l g k AH EF GF KL) := by sorry

  euclid_sentence "1.44.14"
    "and $HK$ its diagonal."
    (step14 : b.onLine HB ∧ between h b k) := by sorry

  euclid_sentence "1.44.15"
    "And $AG$ and $ME$ (are) parallelograms,"
    (step15 : formParallelogram h a f b AH BG GF AB ∧ formParallelogram b m e k BG EF AB KL) := by sorry

  euclid_sentence "1.44.16"
    "and $LB$ and $BF$ the so-called complements, about $HK$."
    (step16 : formParallelogram b m a l BG AH AB KL ∧ formParallelogram f g b e GF AB BG EF) := by sorry

  euclid_sentence "1.44.17"
    "Thus, $LB$ is equal to $BF$ [Prop.~1.43]."
    (step17 : Triangle.area △ a:b:m + Triangle.area △ a:l:m =
      Triangle.area △ f:g:e + Triangle.area △ f:e:b) := by sorry

  euclid_sentence "1.44.18"
    "But, $BF$ is equal to triangle $C$."
    (step18 : Triangle.area △ f:g:e + Triangle.area △ f:e:b = Triangle.area △ c₁:c₂:c₃) := by sorry

  euclid_sentence "1.44.19"
    "Thus, $LB$ is also equal to $C$."
    (step19 : Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) := by sorry

  -- @assumption_gap
  have step20_assumption1 : ∠ e:b:f = ∠ a:b:m := by sorry
  -- @assumption_valid
  have step20_assumption2 : ∠ e:b:f = ∠ d₁:d₂:d₃ := by assumption
  -- @assumption ("angle $GBE$ is equal to $ABM$", ∠ e:b:f = ∠ a:b:m)
  -- @assumption ("$GBE$ is equal to $D$", ∠ e:b:f = ∠ d₁:d₂:d₃)
  euclid_sentence "1.44.20"
    "Also, since angle $GBE$ is equal to $ABM$ [Prop.~1.15], but $GBE$ is equal to $D$, $ABM$ is thus also equal to angle $D$. "
    (step20 : ∠ a:b:m = ∠ d₁:d₂:d₃) := by sorry

  exact ⟨m, l, BG, AH, KL, step16.1, step20, step19⟩
  euclid_conclude_sentence "1.44.21"
    "Thus, the parallelogram $LB$, equal to the given triangle $C$, has been applied to the given straight-line $AB$ in the angle $ABM$, which is equal to $D$. (Which is) the very thing it was required to do."

end Elements.Book1
