/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 3019–3033 of 4715

File 238 of 351: the parts `rows22250R_3019` … `rows22250R_3033` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 94392 in units of a depth-4 test: row 112 columns 59–63, row 112
columns 64–68, row 112 columns 69–72, row 112 columns 73–75, row 112 columns 76–78, row 112 columns 79–81, row 112
columns 82–84, row 112 columns 85–87, row 112 columns 88–89, row 112 columns 90–91, row 112 columns 92–93, row 112
columns 94–95, row 112 columns 96–96, row 112 columns 97–97, row 112 columns 98–339), each a sum of refined costs
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

theorem rows22250R_3019 : rowsJ2 112 113 59 64 ≤ 2819089969043 := by decide +kernel

theorem rows22250R_3020 : rowsJ2 112 113 64 69 ≤ 1356440010523 := by decide +kernel

theorem rows22250R_3021 : rowsJ2 112 113 69 73 ≤ 0 := by decide +kernel

theorem rows22250R_3022 : rowsJ2 112 113 73 76 ≤ 14366968926 := by decide +kernel

theorem rows22250R_3023 : rowsJ2 112 113 76 79 ≤ 171007868199 := by decide +kernel

theorem rows22250R_3024 : rowsJ2 112 113 79 82 ≤ 14618004915 := by decide +kernel

theorem rows22250R_3025 : rowsJ2 112 113 82 85 ≤ 1214956843935 := by decide +kernel

theorem rows22250R_3026 : rowsJ2 112 113 85 88 ≤ 4702269539566 := by decide +kernel

theorem rows22250R_3027 : rowsJ2 112 113 88 90 ≤ 6142282352714 := by decide +kernel

theorem rows22250R_3028 : rowsJ2 112 113 90 92 ≤ 9358229130937 := by decide +kernel

theorem rows22250R_3029 : rowsJ2 112 113 92 94 ≤ 13311895087504 := by decide +kernel

theorem rows22250R_3030 : rowsJ2 112 113 94 96 ≤ 18051467107424 := by decide +kernel

theorem rows22250R_3031 : rowsJ2 112 113 96 97 ≤ 11056547029295 := by decide +kernel

theorem rows22250R_3032 : rowsJ2 112 113 97 98 ≤ 12575986138272 := by decide +kernel

theorem rows22250R_3033 : rowsJ2 112 113 98 340 ≤ 1458542470628134 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_3019
#print axioms SieveCert.rows22250R_3033
