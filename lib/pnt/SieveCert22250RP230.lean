/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2897–2913 of 4715

File 230 of 351: the parts `rows22250R_2897` … `rows22250R_2913` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 97587 tests: row 107 columns 93–94, row 107 columns 95–95, row 107 columns
96–96, row 107 columns 97–97, row 107 columns 98–98, row 107 columns 99–99, row 107 columns 100–339, row 108 columns
0–25, row 108 columns 26–30, row 108 columns 31–32, row 108 columns 33–34, row 108 columns 35–35, row 108 columns
36–36, row 108 columns 37–38, row 108 columns 39–40, row 108 columns 41–42, row 108 columns 43–45), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2897 : rowsJ2 107 108 93 95 ≤ 11277745969117 := by decide +kernel

theorem rows22250R_2898 : rowsJ2 107 108 95 96 ≤ 7137577761832 := by decide +kernel

theorem rows22250R_2899 : rowsJ2 107 108 96 97 ≤ 8276095422088 := by decide +kernel

theorem rows22250R_2900 : rowsJ2 107 108 97 98 ≤ 9483477522333 := by decide +kernel

theorem rows22250R_2901 : rowsJ2 107 108 98 99 ≤ 10815990941577 := by decide +kernel

theorem rows22250R_2902 : rowsJ2 107 108 99 100 ≤ 12223416645783 := by decide +kernel

theorem rows22250R_2903 : rowsJ2 107 108 100 340 ≤ 816171439241890 := by decide +kernel

theorem rows22250R_2904 : rowsJ2 108 109 0 26 ≤ 0 := by decide +kernel

theorem rows22250R_2905 : rowsJ2 108 109 26 31 ≤ 7752379715871 := by decide +kernel

theorem rows22250R_2906 : rowsJ2 108 109 31 33 ≤ 11401352859877 := by decide +kernel

theorem rows22250R_2907 : rowsJ2 108 109 33 35 ≤ 18617777813141 := by decide +kernel

theorem rows22250R_2908 : rowsJ2 108 109 35 36 ≤ 12930671264458 := by decide +kernel

theorem rows22250R_2909 : rowsJ2 108 109 36 37 ≤ 13719514927306 := by decide +kernel

theorem rows22250R_2910 : rowsJ2 108 109 37 39 ≤ 23184747063486 := by decide +kernel

theorem rows22250R_2911 : rowsJ2 108 109 39 41 ≤ 16023318662640 := by decide +kernel

theorem rows22250R_2912 : rowsJ2 108 109 41 43 ≤ 10434385685364 := by decide +kernel

theorem rows22250R_2913 : rowsJ2 108 109 43 46 ≤ 8301313169229 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2897
#print axioms SieveCert.rows22250R_2913
