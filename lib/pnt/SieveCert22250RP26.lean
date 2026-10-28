/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 301–309 of 4715

File 26 of 351: the parts `rows22250R_301` … `rows22250R_309` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, work 90258 in units of a depth-4 test: row 41 columns 24–25, row 41 columns
26–26, row 41 columns 27–27, row 41 columns 28–28, row 41 columns 29–29, row 41 columns 30–30, row 41 columns 31–31,
row 41 columns 32–32, row 41 columns 33–33), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_301 : rowsJ2 41 42 24 26 ≤ 1119219437264 := by decide +kernel

theorem rows22250R_302 : rowsJ2 41 42 26 27 ≤ 478754141117 := by decide +kernel

theorem rows22250R_303 : rowsJ2 41 42 27 28 ≤ 431259557519 := by decide +kernel

theorem rows22250R_304 : rowsJ2 41 42 28 29 ≤ 401656341786 := by decide +kernel

theorem rows22250R_305 : rowsJ2 41 42 29 30 ≤ 386855829411 := by decide +kernel

theorem rows22250R_306 : rowsJ2 41 42 30 31 ≤ 400541713338 := by decide +kernel

theorem rows22250R_307 : rowsJ2 41 42 31 32 ≤ 417012718815 := by decide +kernel

theorem rows22250R_308 : rowsJ2 41 42 32 33 ≤ 408897483927 := by decide +kernel

theorem rows22250R_309 : rowsJ2 41 42 33 34 ≤ 387236911192 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_301
#print axioms SieveCert.rows22250R_309
