/-
# The refined certificate at `L = 893/400` with `n = 300`, parts 515–521 of 561

File 132 of 142: the parts `rows22325R_515` … `rows22325R_521` of `SieveCert22325R.lean`'s certificate on
`SieveGrid22325R.grid22325R` (7 parts, 28166 tests: row 150 columns 39–299, row 151 columns 0–38, row 151 columns
39–299, row 152 columns 0–84, row 152 columns 85–299, row 153 columns 0–95, row 153 columns 96–299), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22325R.lean`.
-/
import SieveGrid22325R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22325R

theorem rows22325R_515 : rowsJ2 150 151 39 300 ≤ 2918396975001554 := by decide +kernel

theorem rows22325R_516 : rowsJ2 151 152 0 39 ≤ 227019937458463 := by decide +kernel

theorem rows22325R_517 : rowsJ2 151 152 39 300 ≤ 2919404519624050 := by decide +kernel

theorem rows22325R_518 : rowsJ2 152 153 0 85 ≤ 348018818461329 := by decide +kernel

theorem rows22325R_519 : rowsJ2 152 153 85 300 ≤ 2812660197109510 := by decide +kernel

theorem rows22325R_520 : rowsJ2 153 154 0 96 ≤ 1493547871362549 := by decide +kernel

theorem rows22325R_521 : rowsJ2 153 154 96 300 ≤ 1680561366028488 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22325R_515
#print axioms SieveCert.rows22325R_521
