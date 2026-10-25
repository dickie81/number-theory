/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 250–257 of 5796

File 18 of 465: the parts `rows22250R_250` … `rows22250R_257` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 97182 tests: row 37 columns 35–35, row 37 columns 36–36, row 37 columns
37–359, row 38 columns 0–13, row 38 columns 14–16, row 38 columns 17–18, row 38 columns 19–20, row 38 columns
21–22), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_250 : rowsJ2 37 38 35 36 ≤ 654920706048 := by decide +kernel

theorem rows22250R_251 : rowsJ2 37 38 36 37 ≤ 669254966949 := by decide +kernel

theorem rows22250R_252 : rowsJ2 37 38 37 360 ≤ 665200608647 := by decide +kernel

theorem rows22250R_253 : rowsJ2 38 39 0 14 ≤ 461808733538 := by decide +kernel

theorem rows22250R_254 : rowsJ2 38 39 14 17 ≤ 1482486154201 := by decide +kernel

theorem rows22250R_255 : rowsJ2 38 39 17 19 ≤ 1603918837772 := by decide +kernel

theorem rows22250R_256 : rowsJ2 38 39 19 21 ≤ 1826640866812 := by decide +kernel

theorem rows22250R_257 : rowsJ2 38 39 21 23 ≤ 1875985376405 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_250
#print axioms SieveCert.rows22250R_257
