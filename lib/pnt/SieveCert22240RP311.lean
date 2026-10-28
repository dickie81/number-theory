/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 3931–3946 of 5066

File 311 of 387: the parts `rows22240R_3931` … `rows22240R_3946` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99357 in units of a depth-4 test: row 136 columns 73–73, row 136
columns 74–74, row 136 columns 75–76, row 136 columns 77–78, row 136 columns 79–81, row 136 columns 82–85, row 136
columns 86–339, row 137 columns 0–23, row 137 columns 24–35, row 137 columns 36–51, row 137 columns 52–53, row 137
columns 54–55, row 137 columns 56–56, row 137 columns 57–57, row 137 columns 58–58, row 137 columns 59–59), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_3931 : rowsJ2 136 137 73 74 ≤ 4507342204538 := by decide +kernel

theorem rows22240R_3932 : rowsJ2 136 137 74 75 ≤ 3862761162353 := by decide +kernel

theorem rows22240R_3933 : rowsJ2 136 137 75 77 ≤ 5970980418244 := by decide +kernel

theorem rows22240R_3934 : rowsJ2 136 137 77 79 ≤ 3962456920236 := by decide +kernel

theorem rows22240R_3935 : rowsJ2 136 137 79 82 ≤ 4097205836411 := by decide +kernel

theorem rows22240R_3936 : rowsJ2 136 137 82 86 ≤ 18661759773823 := by decide +kernel

theorem rows22240R_3937 : rowsJ2 136 137 86 340 ≤ 532630199633587 := by decide +kernel

theorem rows22240R_3938 : rowsJ2 137 138 0 24 ≤ 5759129238613 := by decide +kernel

theorem rows22240R_3939 : rowsJ2 137 138 24 36 ≤ 6069846169745 := by decide +kernel

theorem rows22240R_3940 : rowsJ2 137 138 36 52 ≤ 6113676964247 := by decide +kernel

theorem rows22240R_3941 : rowsJ2 137 138 52 54 ≤ 5607146607898 := by decide +kernel

theorem rows22240R_3942 : rowsJ2 137 138 54 56 ≤ 8122468078537 := by decide +kernel

theorem rows22240R_3943 : rowsJ2 137 138 56 57 ≤ 5122945471039 := by decide +kernel

theorem rows22240R_3944 : rowsJ2 137 138 57 58 ≤ 5889969566488 := by decide +kernel

theorem rows22240R_3945 : rowsJ2 137 138 58 59 ≤ 6699150233400 := by decide +kernel

theorem rows22240R_3946 : rowsJ2 137 138 59 60 ≤ 7548811200820 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_3931
#print axioms SieveCert.rows22240R_3946
