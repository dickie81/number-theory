/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4617–4633 of 4715

File 345 of 351: the parts `rows22250R_4617` … `rows22250R_4633` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98351 tests: row 187 columns 37–37, row 187 columns 38–38, row 187 columns
39–39, row 187 columns 40–339, row 188 columns 0–31, row 188 columns 32–33, row 188 columns 34–35, row 188 columns
36–36, row 188 columns 37–37, row 188 columns 38–38, row 188 columns 39–339, row 189 columns 0–30, row 189 columns
31–33, row 189 columns 34–35, row 189 columns 36–36, row 189 columns 37–37, row 189 columns 38–339), each a sum of
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

theorem rows22250R_4617 : rowsJ2 187 188 37 38 ≤ 28530445297680 := by decide +kernel

theorem rows22250R_4618 : rowsJ2 187 188 38 39 ≤ 31128896682913 := by decide +kernel

theorem rows22250R_4619 : rowsJ2 187 188 39 40 ≤ 30767068017970 := by decide +kernel

theorem rows22250R_4620 : rowsJ2 187 188 40 340 ≤ 4123176784219205 := by decide +kernel

theorem rows22250R_4621 : rowsJ2 188 189 0 32 ≤ 29044511924399 := by decide +kernel

theorem rows22250R_4622 : rowsJ2 188 189 32 34 ≤ 28470122140880 := by decide +kernel

theorem rows22250R_4623 : rowsJ2 188 189 34 36 ≤ 42939584445041 := by decide +kernel

theorem rows22250R_4624 : rowsJ2 188 189 36 37 ≤ 27903023376469 := by decide +kernel

theorem rows22250R_4625 : rowsJ2 188 189 37 38 ≤ 30520187262296 := by decide +kernel

theorem rows22250R_4626 : rowsJ2 188 189 38 39 ≤ 33082755468224 := by decide +kernel

theorem rows22250R_4627 : rowsJ2 188 189 39 340 ≤ 4253082571124665 := by decide +kernel

theorem rows22250R_4628 : rowsJ2 189 190 0 31 ≤ 22576193408044 := by decide +kernel

theorem rows22250R_4629 : rowsJ2 189 190 31 34 ≤ 41939500391681 := by decide +kernel

theorem rows22250R_4630 : rowsJ2 189 190 34 36 ≤ 46337947807038 := by decide +kernel

theorem rows22250R_4631 : rowsJ2 189 190 36 37 ≤ 29940943546115 := by decide +kernel

theorem rows22250R_4632 : rowsJ2 189 190 37 38 ≤ 32521360784007 := by decide +kernel

theorem rows22250R_4633 : rowsJ2 189 190 38 340 ≤ 4382135552121517 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4617
#print axioms SieveCert.rows22250R_4633
