/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4412–4427 of 4715

File 333 of 351: the parts `rows22250R_4412` … `rows22250R_4427` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 94609 in units of a depth-4 test: row 171 columns 46–46, row 171
columns 47–47, row 171 columns 48–48, row 171 columns 49–49, row 171 columns 50–50, row 171 columns 51–51, row 171
columns 52–53, row 171 columns 54–55, row 171 columns 56–339, row 172 columns 0–36, row 172 columns 37–38, row 172
columns 39–40, row 172 columns 41–41, row 172 columns 42–42, row 172 columns 43–43, row 172 columns 44–44), each a
sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async
false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4412 : rowsJ2 171 172 46 47 ≤ 21833740958304 := by decide +kernel

theorem rows22250R_4413 : rowsJ2 171 172 47 48 ≤ 21601546524922 := by decide +kernel

theorem rows22250R_4414 : rowsJ2 171 172 48 49 ≤ 19364448757707 := by decide +kernel

theorem rows22250R_4415 : rowsJ2 171 172 49 50 ≤ 17269535769311 := by decide +kernel

theorem rows22250R_4416 : rowsJ2 171 172 50 51 ≤ 15312081179706 := by decide +kernel

theorem rows22250R_4417 : rowsJ2 171 172 51 52 ≤ 13487722948092 := by decide +kernel

theorem rows22250R_4418 : rowsJ2 171 172 52 54 ≤ 22014989293112 := by decide +kernel

theorem rows22250R_4419 : rowsJ2 171 172 54 56 ≤ 16220309463850 := by decide +kernel

theorem rows22250R_4420 : rowsJ2 171 172 56 340 ≤ 2745129125564155 := by decide +kernel

theorem rows22250R_4421 : rowsJ2 172 173 0 37 ≤ 20514400563192 := by decide +kernel

theorem rows22250R_4422 : rowsJ2 172 173 37 39 ≤ 18236909439274 := by decide +kernel

theorem rows22250R_4423 : rowsJ2 172 173 39 41 ≤ 23983335603115 := by decide +kernel

theorem rows22250R_4424 : rowsJ2 172 173 41 42 ≤ 14330855961132 := by decide +kernel

theorem rows22250R_4425 : rowsJ2 172 173 42 43 ≤ 15982833364287 := by decide +kernel

theorem rows22250R_4426 : rowsJ2 172 173 43 44 ≤ 17701150345489 := by decide +kernel

theorem rows22250R_4427 : rowsJ2 172 173 44 45 ≤ 19483720020102 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4412
#print axioms SieveCert.rows22250R_4427
