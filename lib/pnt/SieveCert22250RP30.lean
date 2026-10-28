/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 332–337 of 4715

File 30 of 351: the parts `rows22250R_332` … `rows22250R_337` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (6 parts, work 96125 in units of a depth-4 test: row 42 columns 35–35, row 42 columns
36–36, row 42 columns 37–37, row 42 columns 38–38, row 42 columns 39–39, row 42 columns 40–40), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_332 : rowsJ2 42 43 35 36 ≤ 244861659637 := by decide +kernel

theorem rows22250R_333 : rowsJ2 42 43 36 37 ≤ 211022063805 := by decide +kernel

theorem rows22250R_334 : rowsJ2 42 43 37 38 ≤ 176599409585 := by decide +kernel

theorem rows22250R_335 : rowsJ2 42 43 38 39 ≤ 147497847155 := by decide +kernel

theorem rows22250R_336 : rowsJ2 42 43 39 40 ≤ 117760633657 := by decide +kernel

theorem rows22250R_337 : rowsJ2 42 43 40 41 ≤ 94921091168 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_332
#print axioms SieveCert.rows22250R_337
