/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 2015–2030 of 5066

File 179 of 387: the parts `rows22240R_2015` … `rows22240R_2030` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94676 in units of a depth-4 test: row 83 columns 62–62, row 83 columns
63–63, row 83 columns 64–64, row 83 columns 65–66, row 83 columns 67–68, row 83 columns 69–70, row 83 columns 71–73,
row 83 columns 74–76, row 83 columns 77–78, row 83 columns 79–79, row 83 columns 80–80, row 83 columns 81–81, row 83
columns 82–82, row 83 columns 83–339, row 84 columns 0–16, row 84 columns 17–18), each a sum of refined costs
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

theorem rows22240R_2015 : rowsJ2 83 84 62 63 ≤ 0 := by decide +kernel

theorem rows22240R_2016 : rowsJ2 83 84 63 64 ≤ 0 := by decide +kernel

theorem rows22240R_2017 : rowsJ2 83 84 64 65 ≤ 0 := by decide +kernel

theorem rows22240R_2018 : rowsJ2 83 84 65 67 ≤ 0 := by decide +kernel

theorem rows22240R_2019 : rowsJ2 83 84 67 69 ≤ 0 := by decide +kernel

theorem rows22240R_2020 : rowsJ2 83 84 69 71 ≤ 0 := by decide +kernel

theorem rows22240R_2021 : rowsJ2 83 84 71 74 ≤ 0 := by decide +kernel

theorem rows22240R_2022 : rowsJ2 83 84 74 77 ≤ 67891566111 := by decide +kernel

theorem rows22240R_2023 : rowsJ2 83 84 77 79 ≤ 2198443792499 := by decide +kernel

theorem rows22240R_2024 : rowsJ2 83 84 79 80 ≤ 1731656787169 := by decide +kernel

theorem rows22240R_2025 : rowsJ2 83 84 80 81 ≤ 1996851075269 := by decide +kernel

theorem rows22240R_2026 : rowsJ2 83 84 81 82 ≤ 2148094255122 := by decide +kernel

theorem rows22240R_2027 : rowsJ2 83 84 82 83 ≤ 2551844041822 := by decide +kernel

theorem rows22240R_2028 : rowsJ2 83 84 83 340 ≤ 3076763401172 := by decide +kernel

theorem rows22240R_2029 : rowsJ2 84 85 0 17 ≤ 116210985385 := by decide +kernel

theorem rows22240R_2030 : rowsJ2 84 85 17 19 ≤ 10492938135 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_2015
#print axioms SieveCert.rows22240R_2030
