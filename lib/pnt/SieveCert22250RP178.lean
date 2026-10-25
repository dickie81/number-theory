/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 2139–2150 of 4715

File 178 of 351: the parts `rows22250R_2139` … `rows22250R_2150` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 99554 tests: row 88 columns 87–87, row 88 columns 88–339, row 89 columns
0–15, row 89 columns 16–19, row 89 columns 20–24, row 89 columns 25–31, row 89 columns 32–35, row 89 columns 36–37,
row 89 columns 38–39, row 89 columns 40–40, row 89 columns 41–41, row 89 columns 42–42), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R
-- exclusive-heavy: a part of this file can use over 7 GiB; scripts/lean-slots.sh runs it alone among the parts

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_2139 : rowsJ2 88 89 87 88 ≤ 7632955014576 := by decide +kernel

theorem rows22250R_2140 : rowsJ2 88 89 88 340 ≤ 8808785401716 := by decide +kernel

theorem rows22250R_2141 : rowsJ2 89 90 0 16 ≤ 0 := by decide +kernel

theorem rows22250R_2142 : rowsJ2 89 90 16 20 ≤ 0 := by decide +kernel

theorem rows22250R_2143 : rowsJ2 89 90 20 25 ≤ 0 := by decide +kernel

theorem rows22250R_2144 : rowsJ2 89 90 25 32 ≤ 100464195318 := by decide +kernel

theorem rows22250R_2145 : rowsJ2 89 90 32 36 ≤ 7728972129245 := by decide +kernel

theorem rows22250R_2146 : rowsJ2 89 90 36 38 ≤ 11057902617536 := by decide +kernel

theorem rows22250R_2147 : rowsJ2 89 90 38 40 ≤ 16401974529679 := by decide +kernel

theorem rows22250R_2148 : rowsJ2 89 90 40 41 ≤ 10069228706724 := by decide +kernel

theorem rows22250R_2149 : rowsJ2 89 90 41 42 ≤ 11438294082778 := by decide +kernel

theorem rows22250R_2150 : rowsJ2 89 90 42 43 ≤ 12918018938230 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2139
#print axioms SieveCert.rows22250R_2150
