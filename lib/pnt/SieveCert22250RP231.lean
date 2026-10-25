/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2914–2928 of 4715

File 231 of 351: the parts `rows22250R_2914` … `rows22250R_2928` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 97422 tests: row 108 columns 46–50, row 108 columns 51–61, row 108 columns
62–69, row 108 columns 70–73, row 108 columns 74–76, row 108 columns 77–78, row 108 columns 79–80, row 108 columns
81–82, row 108 columns 83–85, row 108 columns 86–88, row 108 columns 89–90, row 108 columns 91–92, row 108 columns
93–94, row 108 columns 95–95, row 108 columns 96–96), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_2914 : rowsJ2 108 109 46 51 ≤ 2037097213929 := by decide +kernel

theorem rows22250R_2915 : rowsJ2 108 109 51 62 ≤ 336763221347 := by decide +kernel

theorem rows22250R_2916 : rowsJ2 108 109 62 70 ≤ 104050308405 := by decide +kernel

theorem rows22250R_2917 : rowsJ2 108 109 70 74 ≤ 0 := by decide +kernel

theorem rows22250R_2918 : rowsJ2 108 109 74 77 ≤ 102705183558 := by decide +kernel

theorem rows22250R_2919 : rowsJ2 108 109 77 79 ≤ 664713419550 := by decide +kernel

theorem rows22250R_2920 : rowsJ2 108 109 79 81 ≤ 658198272740 := by decide +kernel

theorem rows22250R_2921 : rowsJ2 108 109 81 83 ≤ 463218055264 := by decide +kernel

theorem rows22250R_2922 : rowsJ2 108 109 83 86 ≤ 1481477311000 := by decide +kernel

theorem rows22250R_2923 : rowsJ2 108 109 86 89 ≤ 4292539971506 := by decide +kernel

theorem rows22250R_2924 : rowsJ2 108 109 89 91 ≤ 5545521324529 := by decide +kernel

theorem rows22250R_2925 : rowsJ2 108 109 91 93 ≤ 8463492914760 := by decide +kernel

theorem rows22250R_2926 : rowsJ2 108 109 93 95 ≤ 12063746450520 := by decide +kernel

theorem rows22250R_2927 : rowsJ2 108 109 95 96 ≤ 7613042897903 := by decide +kernel

theorem rows22250R_2928 : rowsJ2 108 109 96 97 ≤ 8774925348028 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2914
#print axioms SieveCert.rows22250R_2928
