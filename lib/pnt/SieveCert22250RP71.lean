/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 656–665 of 5796

File 71 of 465: the parts `rows22250R_656` … `rows22250R_665` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97822 tests: row 53 columns 42–42, row 53 columns 43–43, row 53 columns
44–44, row 53 columns 45–45, row 53 columns 46–46, row 53 columns 47–47, row 53 columns 48–48, row 53 columns 49–49,
row 53 columns 50–50, row 53 columns 51–51), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_656 : rowsJ2 53 54 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_657 : rowsJ2 53 54 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_658 : rowsJ2 53 54 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_659 : rowsJ2 53 54 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_660 : rowsJ2 53 54 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_661 : rowsJ2 53 54 47 48 ≤ 120134375425 := by decide +kernel

theorem rows22250R_662 : rowsJ2 53 54 48 49 ≤ 538422922924 := by decide +kernel

theorem rows22250R_663 : rowsJ2 53 54 49 50 ≤ 1002613820265 := by decide +kernel

theorem rows22250R_664 : rowsJ2 53 54 50 51 ≤ 1507960823968 := by decide +kernel

theorem rows22250R_665 : rowsJ2 53 54 51 52 ≤ 2170704641316 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_656
#print axioms SieveCert.rows22250R_665
