/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5536–5551 of 5796

File 449 of 465: the parts `rows22250R_5536` … `rows22250R_5551` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99161 tests: row 186 columns 52–52, row 186 columns 53–53, row 186 columns
54–359, row 187 columns 0–36, row 187 columns 37–38, row 187 columns 39–40, row 187 columns 41–41, row 187 columns
42–42, row 187 columns 43–43, row 187 columns 44–44, row 187 columns 45–45, row 187 columns 46–46, row 187 columns
47–47, row 187 columns 48–48, row 187 columns 49–49, row 187 columns 50–50), each a sum of refined costs (`rows2` or
`rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5536 : rowsJ2 186 187 52 53 ≤ 13335497714674 := by decide +kernel

theorem rows22250R_5537 : rowsJ2 186 187 53 54 ≤ 11752135809190 := by decide +kernel

theorem rows22250R_5538 : rowsJ2 186 187 54 360 ≤ 2726772757348789 := by decide +kernel

theorem rows22250R_5539 : rowsJ2 187 188 0 37 ≤ 14978997819082 := by decide +kernel

theorem rows22250R_5540 : rowsJ2 187 188 37 39 ≤ 16364207328063 := by decide +kernel

theorem rows22250R_5541 : rowsJ2 187 188 39 41 ≤ 24248541678975 := by decide +kernel

theorem rows22250R_5542 : rowsJ2 187 188 41 42 ≤ 14317586563561 := by decide +kernel

theorem rows22250R_5543 : rowsJ2 187 188 42 43 ≤ 15860332817058 := by decide +kernel

theorem rows22250R_5544 : rowsJ2 187 188 43 44 ≤ 17461026085144 := by decide +kernel

theorem rows22250R_5545 : rowsJ2 187 188 44 45 ≤ 19117993204817 := by decide +kernel

theorem rows22250R_5546 : rowsJ2 187 188 45 46 ≤ 20829790928869 := by decide +kernel

theorem rows22250R_5547 : rowsJ2 187 188 46 47 ≤ 22595197036561 := by decide +kernel

theorem rows22250R_5548 : rowsJ2 187 188 47 48 ≤ 22361772549080 := by decide +kernel

theorem rows22250R_5549 : rowsJ2 187 188 48 49 ≤ 20190832076314 := by decide +kernel

theorem rows22250R_5550 : rowsJ2 187 188 49 50 ≤ 18150471120499 := by decide +kernel

theorem rows22250R_5551 : rowsJ2 187 188 50 51 ≤ 16236289394253 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5536
#print axioms SieveCert.rows22250R_5551
