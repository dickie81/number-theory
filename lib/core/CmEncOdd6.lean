import Mathlib
import CmFinA
import CmFinRp0
import CmFinRp1
import CmFinRp2
import CmFinRp3

/-! # Odd-sector `C^ψ` enclosure at the even-sector tolerance `6·10⁻⁹` -/

namespace CmFin

lemma rows_odd6 (i : ℕ) (hi : i < 28) : rowOK 1 WeilHead.OddQ.cq (6 / 10 ^ 9) i = true := by
  interval_cases i
  exacts [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27]

theorem cmEnc_odd6 : WeilConst.CmEnc 1 WeilHead.OddQ.cq (6 / 10 ^ 9) := by
  intro i hi j hj
  have h := List.all_eq_true.1 (rows_odd6 i hi) j (List.mem_range.2 hj)
  have := entry 1 i j (by norm_num) hi hj _ _ (of_decide_eq_true h)
  push_cast at this; exact this

end CmFin
