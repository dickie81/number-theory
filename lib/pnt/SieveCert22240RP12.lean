/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 177–190 of 5066

File 12 of 387: the parts `rows22240R_177` … `rows22240R_190` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (14 parts, work 96112 in units of a depth-4 test: row 33 columns 31–31, row 33 columns
32–32, row 33 columns 33–339, row 34 columns 0–13, row 34 columns 14–16, row 34 columns 17–18, row 34 columns 19–20,
row 34 columns 21–21, row 34 columns 22–22, row 34 columns 23–23, row 34 columns 24–24, row 34 columns 25–25, row 34
columns 26–26, row 34 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_177 : rowsJ2 33 34 31 32 ≤ 992701709793 := by decide +kernel

theorem rows22240R_178 : rowsJ2 33 34 32 33 ≤ 971277142887 := by decide +kernel

theorem rows22240R_179 : rowsJ2 33 34 33 340 ≤ 989589158570 := by decide +kernel

theorem rows22240R_180 : rowsJ2 34 35 0 14 ≤ 793488317323 := by decide +kernel

theorem rows22240R_181 : rowsJ2 34 35 14 17 ≤ 1520445147219 := by decide +kernel

theorem rows22240R_182 : rowsJ2 34 35 17 19 ≤ 1958917509177 := by decide +kernel

theorem rows22240R_183 : rowsJ2 34 35 19 21 ≤ 2510688512535 := by decide +kernel

theorem rows22240R_184 : rowsJ2 34 35 21 22 ≤ 1348557864170 := by decide +kernel

theorem rows22240R_185 : rowsJ2 34 35 22 23 ≤ 1383493872179 := by decide +kernel

theorem rows22240R_186 : rowsJ2 34 35 23 24 ≤ 1391927007930 := by decide +kernel

theorem rows22240R_187 : rowsJ2 34 35 24 25 ≤ 1368197607705 := by decide +kernel

theorem rows22240R_188 : rowsJ2 34 35 25 26 ≤ 1313209919907 := by decide +kernel

theorem rows22240R_189 : rowsJ2 34 35 26 27 ≤ 1251247283355 := by decide +kernel

theorem rows22240R_190 : rowsJ2 34 35 27 28 ≤ 1177307187730 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_177
#print axioms SieveCert.rows22240R_190
