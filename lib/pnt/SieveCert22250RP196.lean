/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2044–2057 of 5796

File 196 of 465: the parts `rows22250R_2044` … `rows22250R_2057` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93937 tests: row 83 columns 60–60, row 83 columns 61–61, row 83 columns
62–62, row 83 columns 63–63, row 83 columns 64–64, row 83 columns 65–65, row 83 columns 66–66, row 83 columns 67–67,
row 83 columns 68–68, row 83 columns 69–69, row 83 columns 70–70, row 83 columns 71–71, row 83 columns 72–72, row 83
columns 73–74), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_2044 : rowsJ2 83 84 60 61 ≤ 659694933470 := by decide +kernel

theorem rows22250R_2045 : rowsJ2 83 84 61 62 ≤ 566984023718 := by decide +kernel

theorem rows22250R_2046 : rowsJ2 83 84 62 63 ≤ 475053337894 := by decide +kernel

theorem rows22250R_2047 : rowsJ2 83 84 63 64 ≤ 380792365194 := by decide +kernel

theorem rows22250R_2048 : rowsJ2 83 84 64 65 ≤ 287243633402 := by decide +kernel

theorem rows22250R_2049 : rowsJ2 83 84 65 66 ≤ 191214486372 := by decide +kernel

theorem rows22250R_2050 : rowsJ2 83 84 66 67 ≤ 95828333087 := by decide +kernel

theorem rows22250R_2051 : rowsJ2 83 84 67 68 ≤ 47766975749 := by decide +kernel

theorem rows22250R_2052 : rowsJ2 83 84 68 69 ≤ 0 := by decide +kernel

theorem rows22250R_2053 : rowsJ2 83 84 69 70 ≤ 0 := by decide +kernel

theorem rows22250R_2054 : rowsJ2 83 84 70 71 ≤ 0 := by decide +kernel

theorem rows22250R_2055 : rowsJ2 83 84 71 72 ≤ 0 := by decide +kernel

theorem rows22250R_2056 : rowsJ2 83 84 72 73 ≤ 0 := by decide +kernel

theorem rows22250R_2057 : rowsJ2 83 84 73 75 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2044
#print axioms SieveCert.rows22250R_2057
