/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 487–498 of 4715

File 48 of 351: the parts `rows22250R_487` … `rows22250R_498` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, work 99437 in units of a depth-4 test: row 48 columns 41–41, row 48 columns
42–42, row 48 columns 43–43, row 48 columns 44–44, row 48 columns 45–45, row 48 columns 46–46, row 48 columns 47–47,
row 48 columns 48–339, row 49 columns 0–14, row 49 columns 15–19, row 49 columns 20–22, row 49 columns 23–24), each
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

theorem rows22250R_487 : rowsJ2 48 49 41 42 ≤ 3466414423 := by decide +kernel

theorem rows22250R_488 : rowsJ2 48 49 42 43 ≤ 2780425286 := by decide +kernel

theorem rows22250R_489 : rowsJ2 48 49 43 44 ≤ 1389983546 := by decide +kernel

theorem rows22250R_490 : rowsJ2 48 49 44 45 ≤ 78334569526 := by decide +kernel

theorem rows22250R_491 : rowsJ2 48 49 45 46 ≤ 304745515863 := by decide +kernel

theorem rows22250R_492 : rowsJ2 48 49 46 47 ≤ 909162131517 := by decide +kernel

theorem rows22250R_493 : rowsJ2 48 49 47 48 ≤ 1805454967384 := by decide +kernel

theorem rows22250R_494 : rowsJ2 48 49 48 340 ≤ 2667830022132 := by decide +kernel

theorem rows22250R_495 : rowsJ2 49 50 0 15 ≤ 2726184597543 := by decide +kernel

theorem rows22250R_496 : rowsJ2 49 50 15 20 ≤ 2607232002711 := by decide +kernel

theorem rows22250R_497 : rowsJ2 49 50 20 23 ≤ 1011635496235 := by decide +kernel

theorem rows22250R_498 : rowsJ2 49 50 23 25 ≤ 472067199513 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_487
#print axioms SieveCert.rows22250R_498
