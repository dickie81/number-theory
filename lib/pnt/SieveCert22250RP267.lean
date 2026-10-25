/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2948–2962 of 5796

File 267 of 465: the parts `rows22250R_2948` … `rows22250R_2962` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94766 tests: row 102 columns 44–44, row 102 columns 45–45, row 102 columns
46–46, row 102 columns 47–47, row 102 columns 48–48, row 102 columns 49–49, row 102 columns 50–50, row 102 columns
51–51, row 102 columns 52–52, row 102 columns 53–53, row 102 columns 54–55, row 102 columns 56–57, row 102 columns
58–59, row 102 columns 60–62, row 102 columns 63–67), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2948 : rowsJ2 102 103 44 45 ≤ 14471205371297 := by decide +kernel

theorem rows22250R_2949 : rowsJ2 102 103 45 46 ≤ 12887809276127 := by decide +kernel

theorem rows22250R_2950 : rowsJ2 102 103 46 47 ≤ 11370411945541 := by decide +kernel

theorem rows22250R_2951 : rowsJ2 102 103 47 48 ≤ 9869451921702 := by decide +kernel

theorem rows22250R_2952 : rowsJ2 102 103 48 49 ≤ 8514607880250 := by decide +kernel

theorem rows22250R_2953 : rowsJ2 102 103 49 50 ≤ 7252842603494 := by decide +kernel

theorem rows22250R_2954 : rowsJ2 102 103 50 51 ≤ 6130078335402 := by decide +kernel

theorem rows22250R_2955 : rowsJ2 102 103 51 52 ≤ 5143750776490 := by decide +kernel

theorem rows22250R_2956 : rowsJ2 102 103 52 53 ≤ 4218131580649 := by decide +kernel

theorem rows22250R_2957 : rowsJ2 102 103 53 54 ≤ 3353607805939 := by decide +kernel

theorem rows22250R_2958 : rowsJ2 102 103 54 56 ≤ 4360582981436 := by decide +kernel

theorem rows22250R_2959 : rowsJ2 102 103 56 58 ≤ 1408172010430 := by decide +kernel

theorem rows22250R_2960 : rowsJ2 102 103 58 60 ≤ 134889552698 := by decide +kernel

theorem rows22250R_2961 : rowsJ2 102 103 60 63 ≤ 0 := by decide +kernel

theorem rows22250R_2962 : rowsJ2 102 103 63 68 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2948
#print axioms SieveCert.rows22250R_2962
