/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 580–592 of 4715

File 57 of 351: the parts `rows22250R_580` … `rows22250R_592` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, 99755 tests: row 51 columns 47–47, row 51 columns 48–48, row 51 columns
49–49, row 51 columns 50–50, row 51 columns 51–339, row 52 columns 0–14, row 52 columns 15–19, row 52 columns 20–22,
row 52 columns 23–24, row 52 columns 25–25, row 52 columns 26–26, row 52 columns 27–27, row 52 columns 28–28), each
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

theorem rows22250R_580 : rowsJ2 51 52 47 48 ≤ 1750204061435 := by decide +kernel

theorem rows22250R_581 : rowsJ2 51 52 48 49 ≤ 2586188536577 := by decide +kernel

theorem rows22250R_582 : rowsJ2 51 52 49 50 ≤ 3537379977922 := by decide +kernel

theorem rows22250R_583 : rowsJ2 51 52 50 51 ≤ 4752005523963 := by decide +kernel

theorem rows22250R_584 : rowsJ2 51 52 51 340 ≤ 6226196406352 := by decide +kernel

theorem rows22250R_585 : rowsJ2 52 53 0 15 ≤ 2743168460647 := by decide +kernel

theorem rows22250R_586 : rowsJ2 52 53 15 20 ≤ 1931917372581 := by decide +kernel

theorem rows22250R_587 : rowsJ2 52 53 20 23 ≤ 665904616361 := by decide +kernel

theorem rows22250R_588 : rowsJ2 52 53 23 25 ≤ 294252041883 := by decide +kernel

theorem rows22250R_589 : rowsJ2 52 53 25 26 ≤ 112421429717 := by decide +kernel

theorem rows22250R_590 : rowsJ2 52 53 26 27 ≤ 93210437005 := by decide +kernel

theorem rows22250R_591 : rowsJ2 52 53 27 28 ≤ 79610995848 := by decide +kernel

theorem rows22250R_592 : rowsJ2 52 53 28 29 ≤ 63103578376 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_580
#print axioms SieveCert.rows22250R_592
