/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4395–4411 of 4715

File 332 of 351: the parts `rows22250R_4395` … `rows22250R_4411` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 97608 tests: row 170 columns 47–47, row 170 columns 48–48, row 170 columns
49–49, row 170 columns 50–50, row 170 columns 51–51, row 170 columns 52–52, row 170 columns 53–54, row 170 columns
55–56, row 170 columns 57–339, row 171 columns 0–36, row 171 columns 37–38, row 171 columns 39–40, row 171 columns
41–41, row 171 columns 42–42, row 171 columns 43–43, row 171 columns 44–44, row 171 columns 45–45), each a sum of
refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_4395 : rowsJ2 170 171 47 48 ≤ 22298371027073 := by decide +kernel

theorem rows22250R_4396 : rowsJ2 170 171 48 49 ≤ 20036604646500 := by decide +kernel

theorem rows22250R_4397 : rowsJ2 170 171 49 50 ≤ 17916220315727 := by decide +kernel

theorem rows22250R_4398 : rowsJ2 170 171 50 51 ≤ 15932459825008 := by decide +kernel

theorem rows22250R_4399 : rowsJ2 170 171 51 52 ≤ 14080926776104 := by decide +kernel

theorem rows22250R_4400 : rowsJ2 170 171 52 53 ≤ 12357565718837 := by decide +kernel

theorem rows22250R_4401 : rowsJ2 170 171 53 55 ≤ 20039375050016 := by decide +kernel

theorem rows22250R_4402 : rowsJ2 170 171 55 57 ≤ 14596358203448 := by decide +kernel

theorem rows22250R_4403 : rowsJ2 170 171 57 340 ≤ 2722795587102307 := by decide +kernel

theorem rows22250R_4404 : rowsJ2 171 172 0 37 ≤ 17686068758041 := by decide +kernel

theorem rows22250R_4405 : rowsJ2 171 172 37 39 ≤ 16576245521791 := by decide +kernel

theorem rows22250R_4406 : rowsJ2 171 172 39 41 ≤ 22054029493997 := by decide +kernel

theorem rows22250R_4407 : rowsJ2 171 172 41 42 ≤ 13265959672661 := by decide +kernel

theorem rows22250R_4408 : rowsJ2 171 172 42 43 ≤ 14851157520926 := by decide +kernel

theorem rows22250R_4409 : rowsJ2 171 172 43 44 ≤ 16502595596068 := by decide +kernel

theorem rows22250R_4410 : rowsJ2 171 172 44 45 ≤ 18218076282036 := by decide +kernel

theorem rows22250R_4411 : rowsJ2 171 172 45 46 ≤ 19995677611194 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4395
#print axioms SieveCert.rows22250R_4411
