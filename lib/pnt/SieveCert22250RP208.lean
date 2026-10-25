/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 2204–2218 of 5796

File 208 of 465: the parts `rows22250R_2204` … `rows22250R_2218` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96641 tests: row 86 columns 82–83, row 86 columns 84–84, row 86 columns
85–85, row 86 columns 86–359, row 87 columns 0–17, row 87 columns 18–19, row 87 columns 20–21, row 87 columns 22–23,
row 87 columns 24–25, row 87 columns 26–28, row 87 columns 29–31, row 87 columns 32–35, row 87 columns 36–38, row 87
columns 39–40, row 87 columns 41–41), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_2204 : rowsJ2 86 87 82 84 ≤ 1302514745081 := by decide +kernel

theorem rows22250R_2205 : rowsJ2 86 87 84 85 ≤ 1265861546043 := by decide +kernel

theorem rows22250R_2206 : rowsJ2 86 87 85 86 ≤ 1627519613583 := by decide +kernel

theorem rows22250R_2207 : rowsJ2 86 87 86 360 ≤ 1873793484022 := by decide +kernel

theorem rows22250R_2208 : rowsJ2 87 88 0 18 ≤ 29180539803 := by decide +kernel

theorem rows22250R_2209 : rowsJ2 87 88 18 20 ≤ 6566495429 := by decide +kernel

theorem rows22250R_2210 : rowsJ2 87 88 20 22 ≤ 2165517594 := by decide +kernel

theorem rows22250R_2211 : rowsJ2 87 88 22 24 ≤ 0 := by decide +kernel

theorem rows22250R_2212 : rowsJ2 87 88 24 26 ≤ 0 := by decide +kernel

theorem rows22250R_2213 : rowsJ2 87 88 26 29 ≤ 0 := by decide +kernel

theorem rows22250R_2214 : rowsJ2 87 88 29 32 ≤ 0 := by decide +kernel

theorem rows22250R_2215 : rowsJ2 87 88 32 36 ≤ 153512360149 := by decide +kernel

theorem rows22250R_2216 : rowsJ2 87 88 36 39 ≤ 3883767341796 := by decide +kernel

theorem rows22250R_2217 : rowsJ2 87 88 39 41 ≤ 6305732341593 := by decide +kernel

theorem rows22250R_2218 : rowsJ2 87 88 41 42 ≤ 3428642997446 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_2204
#print axioms SieveCert.rows22250R_2218
