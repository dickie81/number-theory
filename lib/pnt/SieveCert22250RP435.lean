/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5322–5336 of 5796

File 435 of 465: the parts `rows22250R_5322` … `rows22250R_5336` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96192 tests: row 175 columns 63–64, row 175 columns 65–359, row 176 columns
0–39, row 176 columns 40–41, row 176 columns 42–43, row 176 columns 44–44, row 176 columns 45–45, row 176 columns
46–46, row 176 columns 47–47, row 176 columns 48–48, row 176 columns 49–49, row 176 columns 50–50, row 176 columns
51–51, row 176 columns 52–52, row 176 columns 53–53), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5322 : rowsJ2 175 176 63 65 ≤ 8839596359366 := by decide +kernel

theorem rows22250R_5323 : rowsJ2 175 176 65 360 ≤ 2541075229133684 := by decide +kernel

theorem rows22250R_5324 : rowsJ2 176 177 0 40 ≤ 9790667294245 := by decide +kernel

theorem rows22250R_5325 : rowsJ2 176 177 40 42 ≤ 10291037975626 := by decide +kernel

theorem rows22250R_5326 : rowsJ2 176 177 42 44 ≤ 14099960961589 := by decide +kernel

theorem rows22250R_5327 : rowsJ2 176 177 44 45 ≤ 8624296183316 := by decide +kernel

theorem rows22250R_5328 : rowsJ2 176 177 45 46 ≤ 9746798417879 := by decide +kernel

theorem rows22250R_5329 : rowsJ2 176 177 46 47 ≤ 10921340840028 := by decide +kernel

theorem rows22250R_5330 : rowsJ2 176 177 47 48 ≤ 12146021065073 := by decide +kernel

theorem rows22250R_5331 : rowsJ2 176 177 48 49 ≤ 13419124861990 := by decide +kernel

theorem rows22250R_5332 : rowsJ2 176 177 49 50 ≤ 14739116859222 := by decide +kernel

theorem rows22250R_5333 : rowsJ2 176 177 50 51 ≤ 16104632256007 := by decide +kernel

theorem rows22250R_5334 : rowsJ2 176 177 51 52 ≤ 17514469482497 := by decide +kernel

theorem rows22250R_5335 : rowsJ2 176 177 52 53 ≤ 18967583760861 := by decide +kernel

theorem rows22250R_5336 : rowsJ2 176 177 53 54 ≤ 17173716883320 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5322
#print axioms SieveCert.rows22250R_5336
