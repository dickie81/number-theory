/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2016–2029 of 4715

File 169 of 351: the parts `rows22250R_2016` … `rows22250R_2029` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, work 93859 in units of a depth-4 test: row 85 columns 85–339, row 86 columns
0–16, row 86 columns 17–19, row 86 columns 20–22, row 86 columns 23–26, row 86 columns 27–32, row 86 columns 33–36,
row 86 columns 37–38, row 86 columns 39–39, row 86 columns 40–40, row 86 columns 41–41, row 86 columns 42–42, row 86
columns 43–43, row 86 columns 44–44), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2016 : rowsJ2 85 86 85 340 ≤ 5028458068091 := by decide +kernel

theorem rows22250R_2017 : rowsJ2 86 87 0 17 ≤ 0 := by decide +kernel

theorem rows22250R_2018 : rowsJ2 86 87 17 20 ≤ 0 := by decide +kernel

theorem rows22250R_2019 : rowsJ2 86 87 20 23 ≤ 0 := by decide +kernel

theorem rows22250R_2020 : rowsJ2 86 87 23 27 ≤ 0 := by decide +kernel

theorem rows22250R_2021 : rowsJ2 86 87 27 33 ≤ 97628219078 := by decide +kernel

theorem rows22250R_2022 : rowsJ2 86 87 33 37 ≤ 8327384422514 := by decide +kernel

theorem rows22250R_2023 : rowsJ2 86 87 37 39 ≤ 11056884787287 := by decide +kernel

theorem rows22250R_2024 : rowsJ2 86 87 39 40 ≤ 7380024580239 := by decide +kernel

theorem rows22250R_2025 : rowsJ2 86 87 40 41 ≤ 8679774301248 := by decide +kernel

theorem rows22250R_2026 : rowsJ2 86 87 41 42 ≤ 9997865831619 := by decide +kernel

theorem rows22250R_2027 : rowsJ2 86 87 42 43 ≤ 11331232844517 := by decide +kernel

theorem rows22250R_2028 : rowsJ2 86 87 43 44 ≤ 9599949421313 := by decide +kernel

theorem rows22250R_2029 : rowsJ2 86 87 44 45 ≤ 7376264786332 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2016
#print axioms SieveCert.rows22250R_2029
