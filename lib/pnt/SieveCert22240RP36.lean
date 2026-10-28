/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 388–398 of 5066

File 36 of 387: the parts `rows22240R_388` … `rows22240R_398` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 91962 in units of a depth-4 test: row 44 columns 17–19, row 44 columns
20–22, row 44 columns 23–24, row 44 columns 25–25, row 44 columns 26–26, row 44 columns 27–27, row 44 columns 28–28,
row 44 columns 29–29, row 44 columns 30–30, row 44 columns 31–31, row 44 columns 32–32), each a sum of refined costs
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

theorem rows22240R_388 : rowsJ2 44 45 17 20 ≤ 2678702371188 := by decide +kernel

theorem rows22240R_389 : rowsJ2 44 45 20 23 ≤ 2460494410707 := by decide +kernel

theorem rows22240R_390 : rowsJ2 44 45 23 25 ≤ 1354747990720 := by decide +kernel

theorem rows22240R_391 : rowsJ2 44 45 25 26 ≤ 584295015823 := by decide +kernel

theorem rows22240R_392 : rowsJ2 44 45 26 27 ≤ 529404143619 := by decide +kernel

theorem rows22240R_393 : rowsJ2 44 45 27 28 ≤ 477690672055 := by decide +kernel

theorem rows22240R_394 : rowsJ2 44 45 28 29 ≤ 438068383608 := by decide +kernel

theorem rows22240R_395 : rowsJ2 44 45 29 30 ≤ 407681730485 := by decide +kernel

theorem rows22240R_396 : rowsJ2 44 45 30 31 ≤ 397038650982 := by decide +kernel

theorem rows22240R_397 : rowsJ2 44 45 31 32 ≤ 394684980208 := by decide +kernel

theorem rows22240R_398 : rowsJ2 44 45 32 33 ≤ 385237799028 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_388
#print axioms SieveCert.rows22240R_398
