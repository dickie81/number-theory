/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4047–4060 of 4715

File 309 of 351: the parts `rows22250R_4047` … `rows22250R_4060` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 97599 tests: row 153 columns 43–45, row 153 columns 46–47, row 153 columns
48–48, row 153 columns 49–49, row 153 columns 50–50, row 153 columns 51–51, row 153 columns 52–52, row 153 columns
53–53, row 153 columns 54–54, row 153 columns 55–55, row 153 columns 56–56, row 153 columns 57–57, row 153 columns
58–58, row 153 columns 59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide
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

theorem rows22250R_4047 : rowsJ2 153 154 43 46 ≤ 11216626569690 := by decide +kernel

theorem rows22250R_4048 : rowsJ2 153 154 46 48 ≤ 11655401145573 := by decide +kernel

theorem rows22250R_4049 : rowsJ2 153 154 48 49 ≤ 7260810215687 := by decide +kernel

theorem rows22250R_4050 : rowsJ2 153 154 49 50 ≤ 8290052326626 := by decide +kernel

theorem rows22250R_4051 : rowsJ2 153 154 50 51 ≤ 9371842202287 := by decide +kernel

theorem rows22250R_4052 : rowsJ2 153 154 51 52 ≤ 10504151994426 := by decide +kernel

theorem rows22250R_4053 : rowsJ2 153 154 52 53 ≤ 11685137499355 := by decide +kernel

theorem rows22250R_4054 : rowsJ2 153 154 53 54 ≤ 12913128625564 := by decide +kernel

theorem rows22250R_4055 : rowsJ2 153 154 54 55 ≤ 14186620805236 := by decide +kernel

theorem rows22250R_4056 : rowsJ2 153 154 55 56 ≤ 15504267291339 := by decide +kernel

theorem rows22250R_4057 : rowsJ2 153 154 56 57 ≤ 15353787389394 := by decide +kernel

theorem rows22250R_4058 : rowsJ2 153 154 57 58 ≤ 13777517812769 := by decide +kernel

theorem rows22250R_4059 : rowsJ2 153 154 58 59 ≤ 12298405939950 := by decide +kernel

theorem rows22250R_4060 : rowsJ2 153 154 59 60 ≤ 10913711424798 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4047
#print axioms SieveCert.rows22250R_4060
