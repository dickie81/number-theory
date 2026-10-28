/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2058–2073 of 5066

File 182 of 387: the parts `rows22240R_2058` … `rows22240R_2073` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 96200 in units of a depth-4 test: row 84 columns 59–59, row 84 columns
60–60, row 84 columns 61–61, row 84 columns 62–62, row 84 columns 63–63, row 84 columns 64–65, row 84 columns 66–67,
row 84 columns 68–69, row 84 columns 70–72, row 84 columns 73–75, row 84 columns 76–77, row 84 columns 78–79, row 84
columns 80–80, row 84 columns 81–81, row 84 columns 82–82, row 84 columns 83–83), each a sum of refined costs
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

theorem rows22240R_2058 : rowsJ2 84 85 59 60 ≤ 0 := by decide +kernel

theorem rows22240R_2059 : rowsJ2 84 85 60 61 ≤ 0 := by decide +kernel

theorem rows22240R_2060 : rowsJ2 84 85 61 62 ≤ 0 := by decide +kernel

theorem rows22240R_2061 : rowsJ2 84 85 62 63 ≤ 0 := by decide +kernel

theorem rows22240R_2062 : rowsJ2 84 85 63 64 ≤ 0 := by decide +kernel

theorem rows22240R_2063 : rowsJ2 84 85 64 66 ≤ 0 := by decide +kernel

theorem rows22240R_2064 : rowsJ2 84 85 66 68 ≤ 0 := by decide +kernel

theorem rows22240R_2065 : rowsJ2 84 85 68 70 ≤ 0 := by decide +kernel

theorem rows22240R_2066 : rowsJ2 84 85 70 73 ≤ 0 := by decide +kernel

theorem rows22240R_2067 : rowsJ2 84 85 73 76 ≤ 0 := by decide +kernel

theorem rows22240R_2068 : rowsJ2 84 85 76 78 ≤ 832465966511 := by decide +kernel

theorem rows22240R_2069 : rowsJ2 84 85 78 80 ≤ 2729294211412 := by decide +kernel

theorem rows22240R_2070 : rowsJ2 84 85 80 81 ≤ 1650581726206 := by decide +kernel

theorem rows22240R_2071 : rowsJ2 84 85 81 82 ≤ 1907833399994 := by decide +kernel

theorem rows22240R_2072 : rowsJ2 84 85 82 83 ≤ 2298795317366 := by decide +kernel

theorem rows22240R_2073 : rowsJ2 84 85 83 84 ≤ 2940629827302 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2058
#print axioms SieveCert.rows22240R_2073
