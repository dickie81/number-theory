/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1728–1735 of 5796

File 171 of 465: the parts `rows22250R_1728` … `rows22250R_1735` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 99054 tests: row 77 columns 55–55, row 77 columns 56–56, row 77 columns
57–57, row 77 columns 58–58, row 77 columns 59–59, row 77 columns 60–60, row 77 columns 61–61, row 77 columns
62–62), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1728 : rowsJ2 77 78 55 56 ≤ 3396331994789 := by decide +kernel

theorem rows22250R_1729 : rowsJ2 77 78 56 57 ≤ 3704862007565 := by decide +kernel

theorem rows22250R_1730 : rowsJ2 77 78 57 58 ≤ 3722262769288 := by decide +kernel

theorem rows22250R_1731 : rowsJ2 77 78 58 59 ≤ 3499155672515 := by decide +kernel

theorem rows22250R_1732 : rowsJ2 77 78 59 60 ≤ 3271328339004 := by decide +kernel

theorem rows22250R_1733 : rowsJ2 77 78 60 61 ≤ 3045903456229 := by decide +kernel

theorem rows22250R_1734 : rowsJ2 77 78 61 62 ≤ 2815419626655 := by decide +kernel

theorem rows22250R_1735 : rowsJ2 77 78 62 63 ≤ 2587174457353 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1728
#print axioms SieveCert.rows22250R_1735
