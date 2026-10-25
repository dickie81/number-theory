/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 451–457 of 4715

File 44 of 351: the parts `rows22250R_451` … `rows22250R_457` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 93704 tests: row 47 columns 32–32, row 47 columns 33–33, row 47 columns
34–34, row 47 columns 35–35, row 47 columns 36–36, row 47 columns 37–37, row 47 columns 38–38), each a sum of
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

theorem rows22250R_451 : rowsJ2 47 48 32 33 ≤ 109216993586 := by decide +kernel

theorem rows22250R_452 : rowsJ2 47 48 33 34 ≤ 85890237681 := by decide +kernel

theorem rows22250R_453 : rowsJ2 47 48 34 35 ≤ 66247447093 := by decide +kernel

theorem rows22250R_454 : rowsJ2 47 48 35 36 ≤ 47861570403 := by decide +kernel

theorem rows22250R_455 : rowsJ2 47 48 36 37 ≤ 33836541174 := by decide +kernel

theorem rows22250R_456 : rowsJ2 47 48 37 38 ≤ 21765493957 := by decide +kernel

theorem rows22250R_457 : rowsJ2 47 48 38 39 ≤ 14073029510 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_451
#print axioms SieveCert.rows22250R_457
