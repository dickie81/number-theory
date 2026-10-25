/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 478–483 of 5796

File 49 of 465: the parts `rows22250R_478` … `rows22250R_483` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, 90827 tests: row 47 columns 41–41, row 47 columns 42–42, row 47 columns
43–43, row 47 columns 44–44, row 47 columns 45–45, row 47 columns 46–46), each a sum of refined costs (`rows2` or
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

theorem rows22250R_478 : rowsJ2 47 48 41 42 ≤ 37231247234 := by decide +kernel

theorem rows22250R_479 : rowsJ2 47 48 42 43 ≤ 26221228476 := by decide +kernel

theorem rows22250R_480 : rowsJ2 47 48 43 44 ≤ 19162216040 := by decide +kernel

theorem rows22250R_481 : rowsJ2 47 48 44 45 ≤ 12145474153 := by decide +kernel

theorem rows22250R_482 : rowsJ2 47 48 45 46 ≤ 9678361335 := by decide +kernel

theorem rows22250R_483 : rowsJ2 47 48 46 47 ≤ 7232557149 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_478
#print axioms SieveCert.rows22250R_483
