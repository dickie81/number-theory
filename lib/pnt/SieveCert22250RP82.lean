/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 874–885 of 4715

File 82 of 351: the parts `rows22250R_874` … `rows22250R_885` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 92202 tests: row 59 columns 59–339, row 60 columns 0–17, row 60 columns
18–21, row 60 columns 22–22, row 60 columns 23–23, row 60 columns 24–24, row 60 columns 25–25, row 60 columns 26–26,
row 60 columns 27–27, row 60 columns 28–28, row 60 columns 29–29, row 60 columns 30–30), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_874 : rowsJ2 59 60 59 340 ≤ 15649738715575 := by decide +kernel

theorem rows22250R_875 : rowsJ2 60 61 0 18 ≤ 2562190927834 := by decide +kernel

theorem rows22250R_876 : rowsJ2 60 61 18 22 ≤ 262644988189 := by decide +kernel

theorem rows22250R_877 : rowsJ2 60 61 22 23 ≤ 27541624816 := by decide +kernel

theorem rows22250R_878 : rowsJ2 60 61 23 24 ≤ 18316078202 := by decide +kernel

theorem rows22250R_879 : rowsJ2 60 61 24 25 ≤ 9170844176 := by decide +kernel

theorem rows22250R_880 : rowsJ2 60 61 25 26 ≤ 4569329418 := by decide +kernel

theorem rows22250R_881 : rowsJ2 60 61 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_882 : rowsJ2 60 61 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_883 : rowsJ2 60 61 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_884 : rowsJ2 60 61 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_885 : rowsJ2 60 61 30 31 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_874
#print axioms SieveCert.rows22250R_885
