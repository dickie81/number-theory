/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2331–2343 of 4715

File 193 of 351: the parts `rows22250R_2331` … `rows22250R_2343` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (13 parts, work 99105 in units of a depth-4 test: row 93 columns 58–60, row 93 columns
61–65, row 93 columns 66–71, row 93 columns 72–76, row 93 columns 77–78, row 93 columns 79–79, row 93 columns 80–80,
row 93 columns 81–81, row 93 columns 82–82, row 93 columns 83–83, row 93 columns 84–84, row 93 columns 85–85, row 93
columns 86–86), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2331 : rowsJ2 93 94 58 61 ≤ 0 := by decide +kernel

theorem rows22250R_2332 : rowsJ2 93 94 61 66 ≤ 0 := by decide +kernel

theorem rows22250R_2333 : rowsJ2 93 94 66 72 ≤ 0 := by decide +kernel

theorem rows22250R_2334 : rowsJ2 93 94 72 77 ≤ 113706784211 := by decide +kernel

theorem rows22250R_2335 : rowsJ2 93 94 77 79 ≤ 742524611935 := by decide +kernel

theorem rows22250R_2336 : rowsJ2 93 94 79 80 ≤ 787771467247 := by decide +kernel

theorem rows22250R_2337 : rowsJ2 93 94 80 81 ≤ 1152942114321 := by decide +kernel

theorem rows22250R_2338 : rowsJ2 93 94 81 82 ≤ 1594756772628 := by decide +kernel

theorem rows22250R_2339 : rowsJ2 93 94 82 83 ≤ 2180403524468 := by decide +kernel

theorem rows22250R_2340 : rowsJ2 93 94 83 84 ≤ 2936311773006 := by decide +kernel

theorem rows22250R_2341 : rowsJ2 93 94 84 85 ≤ 3861040397031 := by decide +kernel

theorem rows22250R_2342 : rowsJ2 93 94 85 86 ≤ 4686274837192 := by decide +kernel

theorem rows22250R_2343 : rowsJ2 93 94 86 87 ≤ 4680714784986 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2331
#print axioms SieveCert.rows22250R_2343
