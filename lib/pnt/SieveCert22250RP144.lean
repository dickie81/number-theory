/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1419–1425 of 5796

File 144 of 465: the parts `rows22250R_1419` … `rows22250R_1425` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (7 parts, 95838 tests: row 71 columns 54–54, row 71 columns 55–55, row 71 columns
56–56, row 71 columns 57–57, row 71 columns 58–58, row 71 columns 59–59, row 71 columns 60–60), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1419 : rowsJ2 71 72 54 55 ≤ 4151390768850 := by decide +kernel

theorem rows22250R_1420 : rowsJ2 71 72 55 56 ≤ 4852442046850 := by decide +kernel

theorem rows22250R_1421 : rowsJ2 71 72 56 57 ≤ 5585296051154 := by decide +kernel

theorem rows22250R_1422 : rowsJ2 71 72 57 58 ≤ 6227525670974 := by decide +kernel

theorem rows22250R_1423 : rowsJ2 71 72 58 59 ≤ 6684380610641 := by decide +kernel

theorem rows22250R_1424 : rowsJ2 71 72 59 60 ≤ 7102212442698 := by decide +kernel

theorem rows22250R_1425 : rowsJ2 71 72 60 61 ≤ 7140429358240 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1419
#print axioms SieveCert.rows22250R_1425
