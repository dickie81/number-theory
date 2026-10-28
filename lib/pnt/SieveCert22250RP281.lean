/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3659–3670 of 4715

File 281 of 351: the parts `rows22250R_3659` … `rows22250R_3670` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 93501 in units of a depth-4 test: row 137 columns 61–61, row 137
columns 62–62, row 137 columns 63–63, row 137 columns 64–64, row 137 columns 65–65, row 137 columns 66–66, row 137
columns 67–67, row 137 columns 68–68, row 137 columns 69–69, row 137 columns 70–70, row 137 columns 71–71, row 137
columns 72–72), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_3659 : rowsJ2 137 138 61 62 ≤ 9801382115867 := by decide +kernel

theorem rows22250R_3660 : rowsJ2 137 138 62 63 ≤ 10581563150394 := by decide +kernel

theorem rows22250R_3661 : rowsJ2 137 138 63 64 ≤ 11315582200996 := by decide +kernel

theorem rows22250R_3662 : rowsJ2 137 138 64 65 ≤ 11081983768481 := by decide +kernel

theorem rows22250R_3663 : rowsJ2 137 138 65 66 ≤ 9994392243521 := by decide +kernel

theorem rows22250R_3664 : rowsJ2 137 138 66 67 ≤ 8960085825917 := by decide +kernel

theorem rows22250R_3665 : rowsJ2 137 138 67 68 ≤ 7998768284313 := by decide +kernel

theorem rows22250R_3666 : rowsJ2 137 138 68 69 ≤ 7086771011745 := by decide +kernel

theorem rows22250R_3667 : rowsJ2 137 138 69 70 ≤ 6244254544268 := by decide +kernel

theorem rows22250R_3668 : rowsJ2 137 138 70 71 ≤ 5447493798046 := by decide +kernel

theorem rows22250R_3669 : rowsJ2 137 138 71 72 ≤ 4717100647366 := by decide +kernel

theorem rows22250R_3670 : rowsJ2 137 138 72 73 ≤ 4029257719270 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3659
#print axioms SieveCert.rows22250R_3670
