/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 231–239 of 5796

File 16 of 465: the parts `rows22250R_231` … `rows22250R_239` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 98686 tests: row 36 columns 34–34, row 36 columns 35–35, row 36 columns
36–359, row 37 columns 0–13, row 37 columns 14–16, row 37 columns 17–18, row 37 columns 19–20, row 37 columns 21–22,
row 37 columns 23–24), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22250R_231 : rowsJ2 36 37 34 35 ≤ 623527370064 := by decide +kernel

theorem rows22250R_232 : rowsJ2 36 37 35 36 ≤ 682259941608 := by decide +kernel

theorem rows22250R_233 : rowsJ2 36 37 36 360 ≤ 713851319013 := by decide +kernel

theorem rows22250R_234 : rowsJ2 37 38 0 14 ≤ 430010921305 := by decide +kernel

theorem rows22250R_235 : rowsJ2 37 38 14 17 ≤ 1422753665465 := by decide +kernel

theorem rows22250R_236 : rowsJ2 37 38 17 19 ≤ 1606236387502 := by decide +kernel

theorem rows22250R_237 : rowsJ2 37 38 19 21 ≤ 1876593056248 := by decide +kernel

theorem rows22250R_238 : rowsJ2 37 38 21 23 ≤ 1963358147645 := by decide +kernel

theorem rows22250R_239 : rowsJ2 37 38 23 25 ≤ 1860912315824 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_231
#print axioms SieveCert.rows22250R_239
