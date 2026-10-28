/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3515–3529 of 5066

File 282 of 387: the parts `rows22240R_3515` … `rows22240R_3529` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (15 parts, work 98166 in units of a depth-4 test: row 122 columns 76–77, row 122
columns 78–81, row 122 columns 82–84, row 122 columns 85–87, row 122 columns 88–89, row 122 columns 90–91, row 122
columns 92–103, row 122 columns 104–339, row 123 columns 0–25, row 123 columns 26–28, row 123 columns 29–31, row 123
columns 32–35, row 123 columns 36–42, row 123 columns 43–56, row 123 columns 57–59), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3515 : rowsJ2 122 123 76 78 ≤ 2194110971664 := by decide +kernel

theorem rows22240R_3516 : rowsJ2 122 123 78 82 ≤ 844621505509 := by decide +kernel

theorem rows22240R_3517 : rowsJ2 122 123 82 85 ≤ 4741763423885 := by decide +kernel

theorem rows22240R_3518 : rowsJ2 122 123 85 88 ≤ 11959417374700 := by decide +kernel

theorem rows22240R_3519 : rowsJ2 122 123 88 90 ≤ 13346260523166 := by decide +kernel

theorem rows22240R_3520 : rowsJ2 122 123 90 92 ≤ 18697068442820 := by decide +kernel

theorem rows22240R_3521 : rowsJ2 122 123 92 104 ≤ 958313086908827 := by decide +kernel

theorem rows22240R_3522 : rowsJ2 122 123 104 340 ≤ 260118848069097 := by decide +kernel

theorem rows22240R_3523 : rowsJ2 123 124 0 26 ≤ 1960094296857 := by decide +kernel

theorem rows22240R_3524 : rowsJ2 123 124 26 29 ≤ 11720412899790 := by decide +kernel

theorem rows22240R_3525 : rowsJ2 123 124 29 32 ≤ 21892355778784 := by decide +kernel

theorem rows22240R_3526 : rowsJ2 123 124 32 36 ≤ 18306673820888 := by decide +kernel

theorem rows22240R_3527 : rowsJ2 123 124 36 43 ≤ 7731233336612 := by decide +kernel

theorem rows22240R_3528 : rowsJ2 123 124 43 57 ≤ 2112614128938 := by decide +kernel

theorem rows22240R_3529 : rowsJ2 123 124 57 60 ≤ 4885535424950 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3515
#print axioms SieveCert.rows22240R_3529
