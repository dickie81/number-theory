/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4193–4207 of 4715

File 319 of 351: the parts `rows22250R_4193` … `rows22250R_4207` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, work 99628 in units of a depth-4 test: row 159 columns 60–61, row 159
columns 62–63, row 159 columns 64–67, row 159 columns 68–339, row 160 columns 0–40, row 160 columns 41–43, row 160
columns 44–45, row 160 columns 46–46, row 160 columns 47–47, row 160 columns 48–48, row 160 columns 49–49, row 160
columns 50–50, row 160 columns 51–51, row 160 columns 52–52, row 160 columns 53–53), each a sum of refined costs
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

theorem rows22250R_4193 : rowsJ2 159 160 60 62 ≤ 12892371970963 := by decide +kernel

theorem rows22250R_4194 : rowsJ2 159 160 62 64 ≤ 9039587739394 := by decide +kernel

theorem rows22250R_4195 : rowsJ2 159 160 64 68 ≤ 9338560677561 := by decide +kernel

theorem rows22250R_4196 : rowsJ2 159 160 68 340 ≤ 2636617431110231 := by decide +kernel

theorem rows22250R_4197 : rowsJ2 160 161 0 41 ≤ 12557158165431 := by decide +kernel

theorem rows22250R_4198 : rowsJ2 160 161 41 44 ≤ 16896099258150 := by decide +kernel

theorem rows22250R_4199 : rowsJ2 160 161 44 46 ≤ 16519355363890 := by decide +kernel

theorem rows22250R_4200 : rowsJ2 160 161 46 47 ≤ 10024858863867 := by decide +kernel

theorem rows22250R_4201 : rowsJ2 160 161 47 48 ≤ 11279390227234 := by decide +kernel

theorem rows22250R_4202 : rowsJ2 160 161 48 49 ≤ 12589449932925 := by decide +kernel

theorem rows22250R_4203 : rowsJ2 160 161 49 50 ≤ 13953075986407 := by decide +kernel

theorem rows22250R_4204 : rowsJ2 160 161 50 51 ≤ 15368511417622 := by decide +kernel

theorem rows22250R_4205 : rowsJ2 160 161 51 52 ≤ 16834194479300 := by decide +kernel

theorem rows22250R_4206 : rowsJ2 160 161 52 53 ≤ 18348749968834 := by decide +kernel

theorem rows22250R_4207 : rowsJ2 160 161 53 54 ≤ 16497618786780 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4193
#print axioms SieveCert.rows22250R_4207
