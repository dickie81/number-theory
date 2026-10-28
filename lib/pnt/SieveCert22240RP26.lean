/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 312–318 of 5066

File 26 of 387: the parts `rows22240R_312` … `rows22240R_318` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (7 parts, work 99390 in units of a depth-4 test: row 40 columns 37–37, row 40 columns
38–38, row 40 columns 39–39, row 40 columns 40–339, row 41 columns 0–13, row 41 columns 14–16, row 41 columns
17–18), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

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

theorem rows22240R_312 : rowsJ2 40 41 37 38 ≤ 498486391507 := by decide +kernel

theorem rows22240R_313 : rowsJ2 40 41 38 39 ≤ 451424460332 := by decide +kernel

theorem rows22240R_314 : rowsJ2 40 41 39 40 ≤ 392273855229 := by decide +kernel

theorem rows22240R_315 : rowsJ2 40 41 40 340 ≤ 347555511181 := by decide +kernel

theorem rows22240R_316 : rowsJ2 41 42 0 14 ≤ 805844998728 := by decide +kernel

theorem rows22240R_317 : rowsJ2 41 42 14 17 ≤ 2073072072419 := by decide +kernel

theorem rows22240R_318 : rowsJ2 41 42 17 19 ≤ 1925885527927 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_312
#print axioms SieveCert.rows22240R_318
