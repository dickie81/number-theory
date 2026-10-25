/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 537–547 of 5796

File 57 of 465: the parts `rows22250R_537` … `rows22250R_547` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 95091 tests: row 49 columns 45–45, row 49 columns 46–46, row 49 columns
47–47, row 49 columns 48–48, row 49 columns 49–359, row 50 columns 0–13, row 50 columns 14–17, row 50 columns 18–21,
row 50 columns 22–23, row 50 columns 24–25, row 50 columns 26–26), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_537 : rowsJ2 49 50 45 46 ≤ 3583336514 := by decide +kernel

theorem rows22250R_538 : rowsJ2 49 50 46 47 ≤ 3084195179 := by decide +kernel

theorem rows22250R_539 : rowsJ2 49 50 47 48 ≤ 127573478669 := by decide +kernel

theorem rows22250R_540 : rowsJ2 49 50 48 49 ≤ 562292323422 := by decide +kernel

theorem rows22250R_541 : rowsJ2 49 50 49 360 ≤ 1044761285005 := by decide +kernel

theorem rows22250R_542 : rowsJ2 50 51 0 14 ≤ 1313520019403 := by decide +kernel

theorem rows22250R_543 : rowsJ2 50 51 14 18 ≤ 2052137529937 := by decide +kernel

theorem rows22250R_544 : rowsJ2 50 51 18 22 ≤ 1772466160424 := by decide +kernel

theorem rows22250R_545 : rowsJ2 50 51 22 24 ≤ 647580130910 := by decide +kernel

theorem rows22250R_546 : rowsJ2 50 51 24 26 ≤ 505779463332 := by decide +kernel

theorem rows22250R_547 : rowsJ2 50 51 26 27 ≤ 206955514071 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_537
#print axioms SieveCert.rows22250R_547
