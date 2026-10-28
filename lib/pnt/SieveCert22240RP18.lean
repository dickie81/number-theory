/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 246–251 of 5066

File 18 of 387: the parts `rows22240R_246` … `rows22240R_251` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (6 parts, work 98945 in units of a depth-4 test: row 37 columns 31–31, row 37 columns
32–32, row 37 columns 33–33, row 37 columns 34–34, row 37 columns 35–35, row 37 columns 36–36), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_246 : rowsJ2 37 38 31 32 ≤ 754337503577 := by decide +kernel

theorem rows22240R_247 : rowsJ2 37 38 32 33 ≤ 780960931291 := by decide +kernel

theorem rows22240R_248 : rowsJ2 37 38 33 34 ≤ 849500033986 := by decide +kernel

theorem rows22240R_249 : rowsJ2 37 38 34 35 ≤ 886450642957 := by decide +kernel

theorem rows22240R_250 : rowsJ2 37 38 35 36 ≤ 900431424757 := by decide +kernel

theorem rows22240R_251 : rowsJ2 37 38 36 37 ≤ 876315079888 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_246
#print axioms SieveCert.rows22240R_251
