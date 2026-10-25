/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 4665–4681 of 4715

File 348 of 351: the parts `rows22250R_4665` … `rows22250R_4681` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 98946 tests: row 199 columns 0–27, row 199 columns 28–339, row 200 columns
0–88, row 200 columns 89–339, rows 201–201, rows 202–202, rows 203–203, rows 204–204, rows 205–205, rows 206–206,
rows 207–208, rows 209–210, rows 211–212, rows 213–214, rows 215–216, rows 217–218, rows 219–220), each a sum of
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

theorem rows22250R_4665 : rowsJ2 199 200 0 28 ≤ 30050350579374 := by decide +kernel

theorem rows22250R_4666 : rowsJ2 199 200 28 340 ≤ 5586588399433968 := by decide +kernel

theorem rows22250R_4667 : rowsJ2 200 201 0 89 ≤ 1617261714243023 := by decide +kernel

theorem rows22250R_4668 : rowsJ2 200 201 89 340 ≤ 4111127777884973 := by decide +kernel

theorem rows22250R_4669 : rows2 201 202 ≤ 5842126387970705 := by decide +kernel

theorem rows22250R_4670 : rows2 202 203 ≤ 5957741425585904 := by decide +kernel

theorem rows22250R_4671 : rows2 203 204 ≤ 6075948543034553 := by decide +kernel

theorem rows22250R_4672 : rows2 204 205 ≤ 6197465162778702 := by decide +kernel

theorem rows22250R_4673 : rows2 205 206 ≤ 6322178752543854 := by decide +kernel

theorem rows22250R_4674 : rows2 206 207 ≤ 6450078027743856 := by decide +kernel

theorem rows22250R_4675 : rows2 207 209 ≤ 13296407860507877 := by decide +kernel

theorem rows22250R_4676 : rows2 209 211 ≤ 13844866750487193 := by decide +kernel

theorem rows22250R_4677 : rows2 211 213 ≤ 14258064602567634 := by decide +kernel

theorem rows22250R_4678 : rows2 213 215 ≤ 14536009628360942 := by decide +kernel

theorem rows22250R_4679 : rows2 215 217 ≤ 14836152822280305 := by decide +kernel

theorem rows22250R_4680 : rows2 217 219 ≤ 15159372936170851 := by decide +kernel

theorem rows22250R_4681 : rows2 219 221 ≤ 15506628340218154 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_4665
#print axioms SieveCert.rows22250R_4681
