import SystemE
import Book1.Prop41.Main

namespace Elements.Book1

theorem helper_1_47_step17 (a b c e h k l m : Point)
    (AL CE DE BC AE AC AH CK HK BK : Line)
    (hpara_CL : formParallelogram l m e c AL CE DE BC)
    (htri_CL : formTriangle a e c AE CE AC)
    (haAL : a.onLine AL) (hpar1 : ¬(AL.intersectsLine CE))
    (hpara_HC : formParallelogram a h c k AH CK AC HK)
    (htri_HC : formTriangle b c k BC CK BK)
    (hbAH : b.onLine AH) (hpar2 : ¬(AH.intersectsLine CK))
    (hce : |(c─e)| = |(b─c)|) (hck : |(c─k)| = |(a─c)|)
    (hang : ∠ e:c:a = ∠ b:c:k) :
    Triangle.area △ c:e:l + Triangle.area △ c:l:m =
      Triangle.area △ a:h:k + Triangle.area △ a:k:c := by
  euclid_apply (proposition_41 l e c m a AL CE DE BC AE AC)
  euclid_apply (proposition_41 a c k h b AH CK AC HK BC BK)
  euclid_finish

end Elements.Book1
