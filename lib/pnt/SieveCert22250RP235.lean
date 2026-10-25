/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2974–2989 of 4715

File 235 of 351: the parts `rows22250R_2974` … `rows22250R_2989` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 97631 tests: row 110 columns 78–80, row 110 columns 81–83, row 110 columns
84–86, row 110 columns 87–88, row 110 columns 89–90, row 110 columns 91–92, row 110 columns 93–94, row 110 columns
95–95, row 110 columns 96–96, row 110 columns 97–97, row 110 columns 98–98, row 110 columns 99–339, row 111 columns
0–26, row 111 columns 27–30, row 111 columns 31–32, row 111 columns 33–34), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2974 : rowsJ2 110 111 78 81 ≤ 393031171544 := by decide +kernel

theorem rows22250R_2975 : rowsJ2 110 111 81 84 ≤ 479567483052 := by decide +kernel

theorem rows22250R_2976 : rowsJ2 110 111 84 87 ≤ 2618000757000 := by decide +kernel

theorem rows22250R_2977 : rowsJ2 110 111 87 89 ≤ 4010854985960 := by decide +kernel

theorem rows22250R_2978 : rowsJ2 110 111 89 91 ≤ 6567948651258 := by decide +kernel

theorem rows22250R_2979 : rowsJ2 110 111 91 93 ≤ 9804531362938 := by decide +kernel

theorem rows22250R_2980 : rowsJ2 110 111 93 95 ≤ 13760819720356 := by decide +kernel

theorem rows22250R_2981 : rowsJ2 110 111 95 96 ≤ 8608241852579 := by decide +kernel

theorem rows22250R_2982 : rowsJ2 110 111 96 97 ≤ 9874982910482 := by decide +kernel

theorem rows22250R_2983 : rowsJ2 110 111 97 98 ≤ 11273320271486 := by decide +kernel

theorem rows22250R_2984 : rowsJ2 110 111 98 99 ≤ 12751864675320 := by decide +kernel

theorem rows22250R_2985 : rowsJ2 110 111 99 340 ≤ 1194313403278099 := by decide +kernel

theorem rows22250R_2986 : rowsJ2 111 112 0 27 ≤ 705060229608 := by decide +kernel

theorem rows22250R_2987 : rowsJ2 111 112 27 31 ≤ 10424663450400 := by decide +kernel

theorem rows22250R_2988 : rowsJ2 111 112 31 33 ≤ 14122714483964 := by decide +kernel

theorem rows22250R_2989 : rowsJ2 111 112 33 35 ≤ 22996242826039 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2974
#print axioms SieveCert.rows22250R_2989
