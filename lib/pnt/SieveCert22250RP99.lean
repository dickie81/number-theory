/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 936–944 of 5796

File 99 of 465: the parts `rows22250R_936` … `rows22250R_944` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 92482 tests: row 61 columns 30–30, row 61 columns 31–31, row 61 columns
32–32, row 61 columns 33–33, row 61 columns 34–34, row 61 columns 35–35, row 61 columns 36–36, row 61 columns 37–37,
row 61 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_936 : rowsJ2 61 62 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_937 : rowsJ2 61 62 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_938 : rowsJ2 61 62 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_939 : rowsJ2 61 62 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_940 : rowsJ2 61 62 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_941 : rowsJ2 61 62 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_942 : rowsJ2 61 62 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_943 : rowsJ2 61 62 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_944 : rowsJ2 61 62 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_936
#print axioms SieveCert.rows22250R_944
