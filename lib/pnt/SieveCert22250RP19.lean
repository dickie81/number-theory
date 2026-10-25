/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 258–268 of 5796

File 19 of 465: the parts `rows22250R_258` … `rows22250R_268` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 93678 tests: row 38 columns 23–24, row 38 columns 25–25, row 38 columns
26–26, row 38 columns 27–27, row 38 columns 28–28, row 38 columns 29–29, row 38 columns 30–30, row 38 columns 31–31,
row 38 columns 32–32, row 38 columns 33–33, row 38 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_258 : rowsJ2 38 39 23 25 ≤ 1743993386999 := by decide +kernel

theorem rows22250R_259 : rowsJ2 38 39 25 26 ≤ 796398274077 := by decide +kernel

theorem rows22250R_260 : rowsJ2 38 39 26 27 ≤ 737191455075 := by decide +kernel

theorem rows22250R_261 : rowsJ2 38 39 27 28 ≤ 670613687963 := by decide +kernel

theorem rows22250R_262 : rowsJ2 38 39 28 29 ≤ 615176166620 := by decide +kernel

theorem rows22250R_263 : rowsJ2 38 39 29 30 ≤ 565557571164 := by decide +kernel

theorem rows22250R_264 : rowsJ2 38 39 30 31 ≤ 531007068902 := by decide +kernel

theorem rows22250R_265 : rowsJ2 38 39 31 32 ≤ 508764756909 := by decide +kernel

theorem rows22250R_266 : rowsJ2 38 39 32 33 ≤ 507550743746 := by decide +kernel

theorem rows22250R_267 : rowsJ2 38 39 33 34 ≤ 531347967132 := by decide +kernel

theorem rows22250R_268 : rowsJ2 38 39 34 35 ≤ 586946744490 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_258
#print axioms SieveCert.rows22250R_268
