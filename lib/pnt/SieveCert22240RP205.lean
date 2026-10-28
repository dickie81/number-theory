/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2371–2383 of 5066

File 205 of 387: the parts `rows22240R_2371` … `rows22240R_2383` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (13 parts, work 89099 in units of a depth-4 test: row 91 columns 57–58, row 91 columns
59–60, row 91 columns 61–62, row 91 columns 63–65, row 91 columns 66–69, row 91 columns 70–73, row 91 columns 74–77,
row 91 columns 78–79, row 91 columns 80–80, row 91 columns 81–81, row 91 columns 82–82, row 91 columns 83–83, row 91
columns 84–84), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_2371 : rowsJ2 91 92 57 59 ≤ 0 := by decide +kernel

theorem rows22240R_2372 : rowsJ2 91 92 59 61 ≤ 0 := by decide +kernel

theorem rows22240R_2373 : rowsJ2 91 92 61 63 ≤ 0 := by decide +kernel

theorem rows22240R_2374 : rowsJ2 91 92 63 66 ≤ 0 := by decide +kernel

theorem rows22240R_2375 : rowsJ2 91 92 66 70 ≤ 0 := by decide +kernel

theorem rows22240R_2376 : rowsJ2 91 92 70 74 ≤ 0 := by decide +kernel

theorem rows22240R_2377 : rowsJ2 91 92 74 78 ≤ 251561871563 := by decide +kernel

theorem rows22240R_2378 : rowsJ2 91 92 78 80 ≤ 1046690760000 := by decide +kernel

theorem rows22240R_2379 : rowsJ2 91 92 80 81 ≤ 995701100573 := by decide +kernel

theorem rows22240R_2380 : rowsJ2 91 92 81 82 ≤ 1466379813692 := by decide +kernel

theorem rows22240R_2381 : rowsJ2 91 92 82 83 ≤ 2091894502544 := by decide +kernel

theorem rows22240R_2382 : rowsJ2 91 92 83 84 ≤ 2864993876539 := by decide +kernel

theorem rows22240R_2383 : rowsJ2 91 92 84 85 ≤ 3813069983005 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2371
#print axioms SieveCert.rows22240R_2383
