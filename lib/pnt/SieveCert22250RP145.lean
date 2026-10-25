/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1426–1432 of 5796

File 145 of 465: the parts `rows22250R_1426` … `rows22250R_1432` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 90294 tests: row 71 columns 61–61, row 71 columns 62–62, row 71 columns
63–63, row 71 columns 64–64, row 71 columns 65–65, row 71 columns 66–66, row 71 columns 67–67), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1426 : rowsJ2 71 72 61 62 ≤ 6770917403522 := by decide +kernel

theorem rows22250R_1427 : rowsJ2 71 72 62 63 ≤ 6405431390642 := by decide +kernel

theorem rows22250R_1428 : rowsJ2 71 72 63 64 ≤ 6031882691870 := by decide +kernel

theorem rows22250R_1429 : rowsJ2 71 72 64 65 ≤ 5662102367388 := by decide +kernel

theorem rows22250R_1430 : rowsJ2 71 72 65 66 ≤ 5283700622257 := by decide +kernel

theorem rows22250R_1431 : rowsJ2 71 72 66 67 ≤ 4908809724928 := by decide +kernel

theorem rows22250R_1432 : rowsJ2 71 72 67 68 ≤ 4579645221111 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1426
#print axioms SieveCert.rows22250R_1432
