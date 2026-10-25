/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4495–4511 of 4715

File 338 of 351: the parts `rows22250R_4495` … `rows22250R_4511` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 95926 tests: row 176 columns 48–48, row 176 columns 49–50, row 176 columns
51–339, row 177 columns 0–34, row 177 columns 35–36, row 177 columns 37–38, row 177 columns 39–39, row 177 columns
40–40, row 177 columns 41–41, row 177 columns 42–42, row 177 columns 43–43, row 177 columns 44–44, row 177 columns
45–45, row 177 columns 46–46, row 177 columns 47–47, row 177 columns 48–49, row 177 columns 50–339), each a sum of
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

theorem rows22250R_4495 : rowsJ2 176 177 48 49 ≤ 15942359334027 := by decide +kernel

theorem rows22250R_4496 : rowsJ2 176 177 49 51 ≤ 26160941755195 := by decide +kernel

theorem rows22250R_4497 : rowsJ2 176 177 51 340 ≤ 2862742369298987 := by decide +kernel

theorem rows22250R_4498 : rowsJ2 177 178 0 35 ≤ 19116441893611 := by decide +kernel

theorem rows22250R_4499 : rowsJ2 177 178 35 37 ≤ 20895878094947 := by decide +kernel

theorem rows22250R_4500 : rowsJ2 177 178 37 39 ≤ 28458641118618 := by decide +kernel

theorem rows22250R_4501 : rowsJ2 177 178 39 40 ≤ 16884492075725 := by decide +kernel

theorem rows22250R_4502 : rowsJ2 177 178 40 41 ≤ 18754664744672 := by decide +kernel

theorem rows22250R_4503 : rowsJ2 177 178 41 42 ≤ 20696792034150 := by decide +kernel

theorem rows22250R_4504 : rowsJ2 177 178 42 43 ≤ 22708805536288 := by decide +kernel

theorem rows22250R_4505 : rowsJ2 177 178 43 44 ≤ 24788955438000 := by decide +kernel

theorem rows22250R_4506 : rowsJ2 177 178 44 45 ≤ 24516645529793 := by decide +kernel

theorem rows22250R_4507 : rowsJ2 177 178 45 46 ≤ 21968559662942 := by decide +kernel

theorem rows22250R_4508 : rowsJ2 177 178 46 47 ≤ 19584445773802 := by decide +kernel

theorem rows22250R_4509 : rowsJ2 177 178 47 48 ≤ 17358518233059 := by decide +kernel

theorem rows22250R_4510 : rowsJ2 177 178 48 50 ≤ 28645793118811 := by decide +kernel

theorem rows22250R_4511 : rowsJ2 177 178 50 340 ≤ 2887818121171644 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4495
#print axioms SieveCert.rows22250R_4511
