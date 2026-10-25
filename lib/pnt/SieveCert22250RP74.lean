/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 779–791 of 4715

File 74 of 351: the parts `rows22250R_779` … `rows22250R_791` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 94695 tests: row 57 columns 41–41, row 57 columns 42–42, row 57 columns
43–43, row 57 columns 44–44, row 57 columns 45–45, row 57 columns 46–46, row 57 columns 47–47, row 57 columns 48–48,
row 57 columns 49–49, row 57 columns 50–50, row 57 columns 51–51, row 57 columns 52–52, row 57 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_779 : rowsJ2 57 58 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_780 : rowsJ2 57 58 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_781 : rowsJ2 57 58 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_782 : rowsJ2 57 58 44 45 ≤ 70925169536 := by decide +kernel

theorem rows22250R_783 : rowsJ2 57 58 45 46 ≤ 278381456897 := by decide +kernel

theorem rows22250R_784 : rowsJ2 57 58 46 47 ≤ 830508951086 := by decide +kernel

theorem rows22250R_785 : rowsJ2 57 58 47 48 ≤ 1649261951432 := by decide +kernel

theorem rows22250R_786 : rowsJ2 57 58 48 49 ≤ 2437031456267 := by decide +kernel

theorem rows22250R_787 : rowsJ2 57 58 49 50 ≤ 3333363425379 := by decide +kernel

theorem rows22250R_788 : rowsJ2 57 58 50 51 ≤ 4477936074058 := by decide +kernel

theorem rows22250R_789 : rowsJ2 57 58 51 52 ≤ 5867103763152 := by decide +kernel

theorem rows22250R_790 : rowsJ2 57 58 52 53 ≤ 7200674562770 := by decide +kernel

theorem rows22250R_791 : rowsJ2 57 58 53 54 ≤ 8622309242216 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_779
#print axioms SieveCert.rows22250R_791
