/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 240–249 of 5796

File 17 of 465: the parts `rows22250R_240` … `rows22250R_249` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 84831 tests: row 37 columns 25–25, row 37 columns 26–26, row 37 columns
27–27, row 37 columns 28–28, row 37 columns 29–29, row 37 columns 30–30, row 37 columns 31–31, row 37 columns 32–32,
row 37 columns 33–33, row 37 columns 34–34), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_240 : rowsJ2 37 38 25 26 ≤ 859689628671 := by decide +kernel

theorem rows22250R_241 : rowsJ2 37 38 26 27 ≤ 800488310904 := by decide +kernel

theorem rows22250R_242 : rowsJ2 37 38 27 28 ≤ 735974973789 := by decide +kernel

theorem rows22250R_243 : rowsJ2 37 38 28 29 ≤ 671638911937 := by decide +kernel

theorem rows22250R_244 : rowsJ2 37 38 29 30 ≤ 619315305884 := by decide +kernel

theorem rows22250R_245 : rowsJ2 37 38 30 31 ≤ 576040541763 := by decide +kernel

theorem rows22250R_246 : rowsJ2 37 38 31 32 ≤ 548884018047 := by decide +kernel

theorem rows22250R_247 : rowsJ2 37 38 32 33 ≤ 541445724019 := by decide +kernel

theorem rows22250R_248 : rowsJ2 37 38 33 34 ≤ 555762216554 := by decide +kernel

theorem rows22250R_249 : rowsJ2 37 38 34 35 ≤ 604927615776 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_240
#print axioms SieveCert.rows22250R_249
