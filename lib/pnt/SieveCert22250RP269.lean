/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2975–2985 of 5796

File 269 of 465: the parts `rows22250R_2975` … `rows22250R_2985` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 93161 tests: row 102 columns 92–92, row 102 columns 93–93, row 102 columns
94–94, row 102 columns 95–95, row 102 columns 96–96, row 102 columns 97–97, row 102 columns 98–98, row 102 columns
99–99, row 102 columns 100–100, row 102 columns 101–101, row 102 columns 102–359), each a sum of refined costs
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

theorem rows22250R_2975 : rowsJ2 102 103 92 93 ≤ 2494830136457 := by decide +kernel

theorem rows22250R_2976 : rowsJ2 102 103 93 94 ≤ 2429002975422 := by decide +kernel

theorem rows22250R_2977 : rowsJ2 102 103 94 95 ≤ 2436719549311 := by decide +kernel

theorem rows22250R_2978 : rowsJ2 102 103 95 96 ≤ 2505871759388 := by decide +kernel

theorem rows22250R_2979 : rowsJ2 102 103 96 97 ≤ 2652848678057 := by decide +kernel

theorem rows22250R_2980 : rowsJ2 102 103 97 98 ≤ 2864528318167 := by decide +kernel

theorem rows22250R_2981 : rowsJ2 102 103 98 99 ≤ 3121312297826 := by decide +kernel

theorem rows22250R_2982 : rowsJ2 102 103 99 100 ≤ 3445063008061 := by decide +kernel

theorem rows22250R_2983 : rowsJ2 102 103 100 101 ≤ 3816839319051 := by decide +kernel

theorem rows22250R_2984 : rowsJ2 102 103 101 102 ≤ 4259310828359 := by decide +kernel

theorem rows22250R_2985 : rowsJ2 102 103 102 360 ≤ 4752160044597 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2975
#print axioms SieveCert.rows22250R_2985
