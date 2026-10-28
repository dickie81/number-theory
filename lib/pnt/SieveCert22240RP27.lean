/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 319–329 of 5066

File 27 of 387: the parts `rows22240R_319` … `rows22240R_329` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 84935 in units of a depth-4 test: row 41 columns 19–20, row 41 columns
21–22, row 41 columns 23–24, row 41 columns 25–25, row 41 columns 26–26, row 41 columns 27–27, row 41 columns 28–28,
row 41 columns 29–29, row 41 columns 30–30, row 41 columns 31–31, row 41 columns 32–32), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_319 : rowsJ2 41 42 19 21 ≤ 2072926646642 := by decide +kernel

theorem rows22240R_320 : rowsJ2 41 42 21 23 ≤ 1978152385209 := by decide +kernel

theorem rows22240R_321 : rowsJ2 41 42 23 25 ≤ 1757175299041 := by decide +kernel

theorem rows22240R_322 : rowsJ2 41 42 25 26 ≤ 775149403917 := by decide +kernel

theorem rows22240R_323 : rowsJ2 41 42 26 27 ≤ 703341657567 := by decide +kernel

theorem rows22240R_324 : rowsJ2 41 42 27 28 ≤ 644707072401 := by decide +kernel

theorem rows22240R_325 : rowsJ2 41 42 28 29 ≤ 593129970499 := by decide +kernel

theorem rows22240R_326 : rowsJ2 41 42 29 30 ≤ 556590073109 := by decide +kernel

theorem rows22240R_327 : rowsJ2 41 42 30 31 ≤ 534968491196 := by decide +kernel

theorem rows22240R_328 : rowsJ2 41 42 31 32 ≤ 534942885349 := by decide +kernel

theorem rows22240R_329 : rowsJ2 41 42 32 33 ≤ 554097920489 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_319
#print axioms SieveCert.rows22240R_329
