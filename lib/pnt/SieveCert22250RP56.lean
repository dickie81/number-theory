/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 531–536 of 5796

File 56 of 465: the parts `rows22250R_531` … `rows22250R_536` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 89141 tests: row 49 columns 39–39, row 49 columns 40–40, row 49 columns
41–41, row 49 columns 42–42, row 49 columns 43–43, row 49 columns 44–44), each a sum of refined costs (`rows2` or
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

theorem rows22250R_531 : rowsJ2 49 50 39 40 ≤ 29948803289 := by decide +kernel

theorem rows22250R_532 : rowsJ2 49 50 40 41 ≤ 19962000164 := by decide +kernel

theorem rows22250R_533 : rowsJ2 49 50 41 42 ≤ 13954674475 := by decide +kernel

theorem rows22250R_534 : rowsJ2 49 50 42 43 ≤ 7982534115 := by decide +kernel

theorem rows22250R_535 : rowsJ2 49 50 43 44 ≤ 6026241671 := by decide +kernel

theorem rows22250R_536 : rowsJ2 49 50 44 45 ≤ 4087282679 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_531
#print axioms SieveCert.rows22250R_536
