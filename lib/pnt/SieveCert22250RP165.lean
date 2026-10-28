/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1958–1973 of 4715

File 165 of 351: the parts `rows22250R_1958` … `rows22250R_1973` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 94607 in units of a depth-4 test: row 84 columns 57–57, row 84 columns
58–58, row 84 columns 59–59, row 84 columns 60–60, row 84 columns 61–62, row 84 columns 63–64, row 84 columns 65–66,
row 84 columns 67–69, row 84 columns 70–73, row 84 columns 74–76, row 84 columns 77–78, row 84 columns 79–79, row 84
columns 80–80, row 84 columns 81–81, row 84 columns 82–82, row 84 columns 83–83), each a sum of refined costs
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

theorem rows22250R_1958 : rowsJ2 84 85 57 58 ≤ 0 := by decide +kernel

theorem rows22250R_1959 : rowsJ2 84 85 58 59 ≤ 0 := by decide +kernel

theorem rows22250R_1960 : rowsJ2 84 85 59 60 ≤ 0 := by decide +kernel

theorem rows22250R_1961 : rowsJ2 84 85 60 61 ≤ 0 := by decide +kernel

theorem rows22250R_1962 : rowsJ2 84 85 61 63 ≤ 0 := by decide +kernel

theorem rows22250R_1963 : rowsJ2 84 85 63 65 ≤ 0 := by decide +kernel

theorem rows22250R_1964 : rowsJ2 84 85 65 67 ≤ 0 := by decide +kernel

theorem rows22250R_1965 : rowsJ2 84 85 67 70 ≤ 0 := by decide +kernel

theorem rows22250R_1966 : rowsJ2 84 85 70 74 ≤ 0 := by decide +kernel

theorem rows22250R_1967 : rowsJ2 84 85 74 77 ≤ 121516784167 := by decide +kernel

theorem rows22250R_1968 : rowsJ2 84 85 77 79 ≤ 917023612856 := by decide +kernel

theorem rows22250R_1969 : rowsJ2 84 85 79 80 ≤ 964398372290 := by decide +kernel

theorem rows22250R_1970 : rowsJ2 84 85 80 81 ≤ 1233516920712 := by decide +kernel

theorem rows22250R_1971 : rowsJ2 84 85 81 82 ≤ 1709384003688 := by decide +kernel

theorem rows22250R_1972 : rowsJ2 84 85 82 83 ≤ 2314620866170 := by decide +kernel

theorem rows22250R_1973 : rowsJ2 84 85 83 84 ≤ 3071416196187 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1958
#print axioms SieveCert.rows22250R_1973
