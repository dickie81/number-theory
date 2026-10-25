/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5427–5440 of 5796

File 442 of 465: the parts `rows22250R_5427` … `rows22250R_5440` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 93614 tests: row 180 columns 60–359, row 181 columns 0–38, row 181 columns
39–40, row 181 columns 41–42, row 181 columns 43–43, row 181 columns 44–44, row 181 columns 45–45, row 181 columns
46–46, row 181 columns 47–47, row 181 columns 48–48, row 181 columns 49–49, row 181 columns 50–50, row 181 columns
51–51, row 181 columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
+kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5427 : rowsJ2 180 181 60 360 ≤ 2599108431474005 := by decide +kernel

theorem rows22250R_5428 : rowsJ2 181 182 0 39 ≤ 13923787460677 := by decide +kernel

theorem rows22250R_5429 : rowsJ2 181 182 39 41 ≤ 14425325602480 := by decide +kernel

theorem rows22250R_5430 : rowsJ2 181 182 41 43 ≤ 18999480058475 := by decide +kernel

theorem rows22250R_5431 : rowsJ2 181 182 43 44 ≤ 11364256707796 := by decide +kernel

theorem rows22250R_5432 : rowsJ2 181 182 44 45 ≤ 12682192475086 := by decide +kernel

theorem rows22250R_5433 : rowsJ2 181 182 45 46 ≤ 14053814061866 := by decide +kernel

theorem rows22250R_5434 : rowsJ2 181 182 46 47 ≤ 15477371023234 := by decide +kernel

theorem rows22250R_5435 : rowsJ2 181 182 47 48 ≤ 16951314032459 := by decide +kernel

theorem rows22250R_5436 : rowsJ2 181 182 48 49 ≤ 18474286005312 := by decide +kernel

theorem rows22250R_5437 : rowsJ2 181 182 49 50 ≤ 20045114353937 := by decide +kernel

theorem rows22250R_5438 : rowsJ2 181 182 50 51 ≤ 19844258975456 := by decide +kernel

theorem rows22250R_5439 : rowsJ2 181 182 51 52 ≤ 17924449209584 := by decide +kernel

theorem rows22250R_5440 : rowsJ2 181 182 52 53 ≤ 16118724479451 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5427
#print axioms SieveCert.rows22250R_5440
