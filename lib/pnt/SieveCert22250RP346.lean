/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4634–4648 of 4715

File 346 of 351: the parts `rows22250R_4634` … `rows22250R_4648` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 96148 in units of a depth-4 test: row 190 columns 0–30, row 190 columns
31–33, row 190 columns 34–35, row 190 columns 36–36, row 190 columns 37–339, row 191 columns 0–30, row 191 columns
31–32, row 191 columns 33–34, row 191 columns 35–35, row 191 columns 36–339, row 192 columns 0–29, row 192 columns
30–32, row 192 columns 33–34, row 192 columns 35–339, row 193 columns 0–29), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4634 : rowsJ2 190 191 0 31 ≤ 26235483277407 := by decide +kernel

theorem rows22250R_4635 : rowsJ2 190 191 31 34 ≤ 45905618071942 := by decide +kernel

theorem rows22250R_4636 : rowsJ2 190 191 34 36 ≤ 49931211421813 := by decide +kernel

theorem rows22250R_4637 : rowsJ2 190 191 36 37 ≤ 31895893080390 := by decide +kernel

theorem rows22250R_4638 : rowsJ2 190 191 37 340 ≤ 4510265945878679 := by decide +kernel

theorem rows22250R_4639 : rowsJ2 191 192 0 31 ≤ 30339921777548 := by decide +kernel

theorem rows22250R_4640 : rowsJ2 191 192 31 33 ≤ 29747131565636 := by decide +kernel

theorem rows22250R_4641 : rowsJ2 191 192 33 35 ≤ 44880900196521 := by decide +kernel

theorem rows22250R_4642 : rowsJ2 191 192 35 36 ≤ 29174371320066 := by decide +kernel

theorem rows22250R_4643 : rowsJ2 191 192 36 340 ≤ 4634641993710830 := by decide +kernel

theorem rows22250R_4644 : rowsJ2 192 193 0 30 ≤ 23590107110992 := by decide +kernel

theorem rows22250R_4645 : rowsJ2 192 193 30 33 ≤ 43834827306629 := by decide +kernel

theorem rows22250R_4646 : rowsJ2 192 193 33 35 ≤ 48452530602647 := by decide +kernel

theorem rows22250R_4647 : rowsJ2 192 193 35 340 ≤ 4756049490045728 := by decide +kernel

theorem rows22250R_4648 : rowsJ2 193 194 0 30 ≤ 27422885052256 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4634
#print axioms SieveCert.rows22250R_4648
