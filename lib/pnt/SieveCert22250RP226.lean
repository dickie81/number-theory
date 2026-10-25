/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2450–2461 of 5796

File 226 of 465: the parts `rows22250R_2450` … `rows22250R_2461` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 96225 tests: row 91 columns 90–90, row 91 columns 91–359, row 92 columns
0–16, row 92 columns 17–19, row 92 columns 20–22, row 92 columns 23–25, row 92 columns 26–30, row 92 columns 31–35,
row 92 columns 36–38, row 92 columns 39–40, row 92 columns 41–41, row 92 columns 42–42), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2450 : rowsJ2 91 92 90 91 ≤ 4426716186074 := by decide +kernel

theorem rows22250R_2451 : rowsJ2 91 92 91 360 ≤ 5450047578316 := by decide +kernel

theorem rows22250R_2452 : rowsJ2 92 93 0 17 ≤ 745955062 := by decide +kernel

theorem rows22250R_2453 : rowsJ2 92 93 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2454 : rowsJ2 92 93 20 23 ≤ 0 := by decide +kernel

theorem rows22250R_2455 : rowsJ2 92 93 23 26 ≤ 0 := by decide +kernel

theorem rows22250R_2456 : rowsJ2 92 93 26 31 ≤ 0 := by decide +kernel

theorem rows22250R_2457 : rowsJ2 92 93 31 36 ≤ 1254590109642 := by decide +kernel

theorem rows22250R_2458 : rowsJ2 92 93 36 39 ≤ 6340425942629 := by decide +kernel

theorem rows22250R_2459 : rowsJ2 92 93 39 41 ≤ 9285033639704 := by decide +kernel

theorem rows22250R_2460 : rowsJ2 92 93 41 42 ≤ 5988376502770 := by decide +kernel

theorem rows22250R_2461 : rowsJ2 92 93 42 43 ≤ 7021324879137 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2450
#print axioms SieveCert.rows22250R_2461
