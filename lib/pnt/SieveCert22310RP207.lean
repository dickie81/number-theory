/-
# The refined certificate at `L = 2231/1000` with `n = 400`, parts 826–830 of 1732

File 207 of 430: the parts `rows22310R_826` … `rows22310R_830` of `SieveCert22310R.lean`'s certificate on
`SieveGrid22310R.grid22310R` (5 parts, 28639 tests: row 123 columns 85–86, row 123 columns 87–88, row 123 columns
89–90, row 123 columns 91–92, row 123 columns 93–94), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22310R.lean`.
-/
import SieveGrid22310R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22310R

theorem rows22310R_826 : rowsJ2 123 124 85 87 ≤ 115621760512 := by decide +kernel

theorem rows22310R_827 : rowsJ2 123 124 87 89 ≤ 393108445217 := by decide +kernel

theorem rows22310R_828 : rowsJ2 123 124 89 91 ≤ 326584096248 := by decide +kernel

theorem rows22310R_829 : rowsJ2 123 124 91 93 ≤ 206081800331 := by decide +kernel

theorem rows22310R_830 : rowsJ2 123 124 93 95 ≤ 111783979288 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22310R_826
#print axioms SieveCert.rows22310R_830
