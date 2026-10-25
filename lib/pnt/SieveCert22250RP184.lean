/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2217–2224 of 4715

File 184 of 351: the parts `rows22250R_2217` … `rows22250R_2224` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 99274 tests: row 90 columns 84–84, row 90 columns 85–85, row 90 columns
86–86, row 90 columns 87–87, row 90 columns 88–88, row 90 columns 89–89, row 90 columns 90–339, row 91 columns
0–15), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_2217 : rowsJ2 90 91 84 85 ≤ 3887258877061 := by decide +kernel

theorem rows22250R_2218 : rowsJ2 90 91 85 86 ≤ 4986154150830 := by decide +kernel

theorem rows22250R_2219 : rowsJ2 90 91 86 87 ≤ 6169866094969 := by decide +kernel

theorem rows22250R_2220 : rowsJ2 90 91 87 88 ≤ 7168254663231 := by decide +kernel

theorem rows22250R_2221 : rowsJ2 90 91 88 89 ≤ 6379742414630 := by decide +kernel

theorem rows22250R_2222 : rowsJ2 90 91 89 90 ≤ 5675524185983 := by decide +kernel

theorem rows22250R_2223 : rowsJ2 90 91 90 340 ≤ 5043403448778 := by decide +kernel

theorem rows22250R_2224 : rowsJ2 91 92 0 16 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2217
#print axioms SieveCert.rows22250R_2224
