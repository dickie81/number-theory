/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 1325–1336 of 5066

File 127 of 387: the parts `rows22240R_1325` … `rows22240R_1336` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (12 parts, work 91024 in units of a depth-4 test: row 69 columns 42–42, row 69 columns
43–43, row 69 columns 44–44, row 69 columns 45–45, row 69 columns 46–46, row 69 columns 47–47, row 69 columns 48–48,
row 69 columns 49–49, row 69 columns 50–50, row 69 columns 51–51, row 69 columns 52–52, row 69 columns 53–53), each
a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_1325 : rowsJ2 69 70 42 43 ≤ 0 := by decide +kernel

theorem rows22240R_1326 : rowsJ2 69 70 43 44 ≤ 0 := by decide +kernel

theorem rows22240R_1327 : rowsJ2 69 70 44 45 ≤ 64518003662 := by decide +kernel

theorem rows22240R_1328 : rowsJ2 69 70 45 46 ≤ 188679167055 := by decide +kernel

theorem rows22240R_1329 : rowsJ2 69 70 46 47 ≤ 367950816430 := by decide +kernel

theorem rows22240R_1330 : rowsJ2 69 70 47 48 ≤ 785605598263 := by decide +kernel

theorem rows22240R_1331 : rowsJ2 69 70 48 49 ≤ 1500899302609 := by decide +kernel

theorem rows22240R_1332 : rowsJ2 69 70 49 50 ≤ 2314583704453 := by decide +kernel

theorem rows22240R_1333 : rowsJ2 69 70 50 51 ≤ 3158232008927 := by decide +kernel

theorem rows22240R_1334 : rowsJ2 69 70 51 52 ≤ 4058620337743 := by decide +kernel

theorem rows22240R_1335 : rowsJ2 69 70 52 53 ≤ 4997393070572 := by decide +kernel

theorem rows22240R_1336 : rowsJ2 69 70 53 54 ≤ 5762903867359 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_1325
#print axioms SieveCert.rows22240R_1336
