/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2336–2343 of 5066

File 202 of 387: the parts `rows22240R_2336` … `rows22240R_2343` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (8 parts, work 86526 in units of a depth-4 test: row 90 columns 81–81, row 90 columns
82–82, row 90 columns 83–83, row 90 columns 84–84, row 90 columns 85–85, row 90 columns 86–86, row 90 columns 87–87,
row 90 columns 88–88), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
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

theorem rows22240R_2336 : rowsJ2 90 91 81 82 ≤ 1477150570071 := by decide +kernel

theorem rows22240R_2337 : rowsJ2 90 91 82 83 ≤ 2102462536138 := by decide +kernel

theorem rows22240R_2338 : rowsJ2 90 91 83 84 ≤ 2872965215033 := by decide +kernel

theorem rows22240R_2339 : rowsJ2 90 91 84 85 ≤ 3815677024733 := by decide +kernel

theorem rows22240R_2340 : rowsJ2 90 91 85 86 ≤ 4925474721192 := by decide +kernel

theorem rows22240R_2341 : rowsJ2 90 91 86 87 ≤ 6233047954244 := by decide +kernel

theorem rows22240R_2342 : rowsJ2 90 91 87 88 ≤ 7638131816644 := by decide +kernel

theorem rows22240R_2343 : rowsJ2 90 91 88 89 ≤ 8867134396190 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2336
#print axioms SieveCert.rows22240R_2343
