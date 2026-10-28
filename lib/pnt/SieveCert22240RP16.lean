/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 225–232 of 5066

File 16 of 387: the parts `rows22240R_225` … `rows22240R_232` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 99628 in units of a depth-4 test: row 36 columns 28–28, row 36 columns
29–29, row 36 columns 30–30, row 36 columns 31–31, row 36 columns 32–32, row 36 columns 33–33, row 36 columns 34–34,
row 36 columns 35–35), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

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

theorem rows22240R_225 : rowsJ2 36 37 28 29 ≤ 934396333523 := by decide +kernel

theorem rows22240R_226 : rowsJ2 36 37 29 30 ≤ 868669958683 := by decide +kernel

theorem rows22240R_227 : rowsJ2 36 37 30 31 ≤ 825513833788 := by decide +kernel

theorem rows22240R_228 : rowsJ2 36 37 31 32 ≤ 803555893108 := by decide +kernel

theorem rows22240R_229 : rowsJ2 36 37 32 33 ≤ 818928092455 := by decide +kernel

theorem rows22240R_230 : rowsJ2 36 37 33 34 ≤ 875751613726 := by decide +kernel

theorem rows22240R_231 : rowsJ2 36 37 34 35 ≤ 938887285747 := by decide +kernel

theorem rows22240R_232 : rowsJ2 36 37 35 36 ≤ 954234372175 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_225
#print axioms SieveCert.rows22240R_232
