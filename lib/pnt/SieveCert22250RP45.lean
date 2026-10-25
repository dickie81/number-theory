/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 458–467 of 4715

File 45 of 351: the parts `rows22250R_458` … `rows22250R_467` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 97668 tests: row 47 columns 39–39, row 47 columns 40–40, row 47 columns
41–41, row 47 columns 42–42, row 47 columns 43–43, row 47 columns 44–44, row 47 columns 45–45, row 47 columns 46–46,
row 47 columns 47–339, row 48 columns 0–14), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_458 : rowsJ2 47 48 39 40 ≤ 8293903769 := by decide +kernel

theorem rows22250R_459 : rowsJ2 47 48 40 41 ≤ 6935649952 := by decide +kernel

theorem rows22250R_460 : rowsJ2 47 48 41 42 ≤ 5550998272 := by decide +kernel

theorem rows22250R_461 : rowsJ2 47 48 42 43 ≤ 4179460731 := by decide +kernel

theorem rows22250R_462 : rowsJ2 47 48 43 44 ≤ 2778783157 := by decide +kernel

theorem rows22250R_463 : rowsJ2 47 48 44 45 ≤ 79857154895 := by decide +kernel

theorem rows22250R_464 : rowsJ2 47 48 45 46 ≤ 308678587379 := by decide +kernel

theorem rows22250R_465 : rowsJ2 47 48 46 47 ≤ 918830762578 := by decide +kernel

theorem rows22250R_466 : rowsJ2 47 48 47 340 ≤ 1824655368904 := by decide +kernel

theorem rows22250R_467 : rowsJ2 48 49 0 15 ≤ 2689424791741 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_458
#print axioms SieveCert.rows22250R_467
