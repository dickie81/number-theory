/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2021–2034 of 5796

File 194 of 465: the parts `rows22250R_2021` … `rows22250R_2034` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 94203 tests: row 83 columns 29–30, row 83 columns 31–33, row 83 columns
34–36, row 83 columns 37–39, row 83 columns 40–41, row 83 columns 42–42, row 83 columns 43–43, row 83 columns 44–44,
row 83 columns 45–45, row 83 columns 46–46, row 83 columns 47–47, row 83 columns 48–48, row 83 columns 49–49, row 83
columns 50–50), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2021 : rowsJ2 83 84 29 31 ≤ 0 := by decide +kernel

theorem rows22250R_2022 : rowsJ2 83 84 31 34 ≤ 0 := by decide +kernel

theorem rows22250R_2023 : rowsJ2 83 84 34 37 ≤ 74550916287 := by decide +kernel

theorem rows22250R_2024 : rowsJ2 83 84 37 40 ≤ 1115616843961 := by decide +kernel

theorem rows22250R_2025 : rowsJ2 83 84 40 42 ≤ 0 := by decide +kernel

theorem rows22250R_2026 : rowsJ2 83 84 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_2027 : rowsJ2 83 84 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_2028 : rowsJ2 83 84 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_2029 : rowsJ2 83 84 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_2030 : rowsJ2 83 84 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_2031 : rowsJ2 83 84 47 48 ≤ 92995328971 := by decide +kernel

theorem rows22250R_2032 : rowsJ2 83 84 48 49 ≤ 416790087485 := by decide +kernel

theorem rows22250R_2033 : rowsJ2 83 84 49 50 ≤ 776117590964 := by decide +kernel

theorem rows22250R_2034 : rowsJ2 83 84 50 51 ≤ 1000637488639 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2021
#print axioms SieveCert.rows22250R_2034
