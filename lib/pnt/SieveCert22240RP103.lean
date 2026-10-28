/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1046–1058 of 5066

File 103 of 387: the parts `rows22240R_1046` … `rows22240R_1058` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 95345 in units of a depth-4 test: row 63 columns 41–41, row 63 columns
42–42, row 63 columns 43–43, row 63 columns 44–44, row 63 columns 45–45, row 63 columns 46–46, row 63 columns 47–47,
row 63 columns 48–48, row 63 columns 49–49, row 63 columns 50–50, row 63 columns 51–51, row 63 columns 52–52, row 63
columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1046 : rowsJ2 63 64 41 42 ≤ 0 := by decide +kernel

theorem rows22240R_1047 : rowsJ2 63 64 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1048 : rowsJ2 63 64 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1049 : rowsJ2 63 64 44 45 ≤ 68048729199 := by decide +kernel

theorem rows22240R_1050 : rowsJ2 63 64 45 46 ≤ 199004569512 := by decide +kernel

theorem rows22240R_1051 : rowsJ2 63 64 46 47 ≤ 388086798178 := by decide +kernel

theorem rows22240R_1052 : rowsJ2 63 64 47 48 ≤ 828597594154 := by decide +kernel

theorem rows22240R_1053 : rowsJ2 63 64 48 49 ≤ 1583035500201 := by decide +kernel

theorem rows22240R_1054 : rowsJ2 63 64 49 50 ≤ 2441248500798 := by decide +kernel

theorem rows22240R_1055 : rowsJ2 63 64 50 51 ≤ 3331065168278 := by decide +kernel

theorem rows22240R_1056 : rowsJ2 63 64 51 52 ≤ 4382847370497 := by decide +kernel

theorem rows22240R_1057 : rowsJ2 63 64 52 53 ≤ 5728574653021 := by decide +kernel

theorem rows22240R_1058 : rowsJ2 63 64 53 54 ≤ 6996492645422 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1046
#print axioms SieveCert.rows22240R_1058
