/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 513–524 of 5796

File 54 of 465: the parts `rows22250R_513` … `rows22250R_524` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99713 tests: row 49 columns 0–13, row 49 columns 14–17, row 49 columns
18–20, row 49 columns 21–23, row 49 columns 24–25, row 49 columns 26–26, row 49 columns 27–27, row 49 columns 28–28,
row 49 columns 29–29, row 49 columns 30–30, row 49 columns 31–31, row 49 columns 32–32), each a sum of refined costs
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

theorem rows22250R_513 : rowsJ2 49 50 0 14 ≤ 1245502058227 := by decide +kernel

theorem rows22250R_514 : rowsJ2 49 50 14 18 ≤ 2141873481146 := by decide +kernel

theorem rows22250R_515 : rowsJ2 49 50 18 21 ≤ 1504279929533 := by decide +kernel

theorem rows22250R_516 : rowsJ2 49 50 21 24 ≤ 1150362653288 := by decide +kernel

theorem rows22250R_517 : rowsJ2 49 50 24 26 ≤ 571976931589 := by decide +kernel

theorem rows22250R_518 : rowsJ2 49 50 26 27 ≤ 235195228584 := by decide +kernel

theorem rows22250R_519 : rowsJ2 49 50 27 28 ≤ 206328179381 := by decide +kernel

theorem rows22250R_520 : rowsJ2 49 50 28 29 ≤ 180965567779 := by decide +kernel

theorem rows22250R_521 : rowsJ2 49 50 29 30 ≤ 165455720835 := by decide +kernel

theorem rows22250R_522 : rowsJ2 49 50 30 31 ≤ 157138391614 := by decide +kernel

theorem rows22250R_523 : rowsJ2 49 50 31 32 ≤ 154257939591 := by decide +kernel

theorem rows22250R_524 : rowsJ2 49 50 32 33 ≤ 139780722189 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_513
#print axioms SieveCert.rows22250R_524
