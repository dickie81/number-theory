/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5741–5757 of 5796

File 462 of 465: the parts `rows22250R_5741` … `rows22250R_5757` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (17 parts, 95311 tests: row 211 columns 29–359, row 212 columns 0–89, row 212 columns
90–359, row 213 columns 0–111, row 213 columns 112–359, rows 214–214, rows 215–215, rows 216–216, rows 217–217, rows
218–218, rows 219–219, rows 220–220, rows 221–222, rows 223–224, rows 225–226, rows 227–228, rows 229–230), each a
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

theorem rows22250R_5741 : rowsJ2 211 212 29 360 ≤ 5300440305859982 := by decide +kernel

theorem rows22250R_5742 : rowsJ2 212 213 0 90 ≤ 1207617990237757 := by decide +kernel

theorem rows22250R_5743 : rowsJ2 212 213 90 360 ≤ 4214768972015613 := by decide +kernel

theorem rows22250R_5744 : rowsJ2 213 214 0 112 ≤ 2858497694874187 := by decide +kernel

theorem rows22250R_5745 : rowsJ2 213 214 112 360 ≤ 2666670905004077 := by decide +kernel

theorem rows22250R_5746 : rows2 214 215 ≤ 5629504729485408 := by decide +kernel

theorem rows22250R_5747 : rows2 215 216 ≤ 5735304278053984 := by decide +kernel

theorem rows22250R_5748 : rows2 216 217 ≤ 5843779180653445 := by decide +kernel

theorem rows22250R_5749 : rows2 217 218 ≤ 5954921273097555 := by decide +kernel

theorem rows22250R_5750 : rows2 218 219 ≤ 6068634551320237 := by decide +kernel

theorem rows22250R_5751 : rows2 219 220 ≤ 6184903230263414 := by decide +kernel

theorem rows22250R_5752 : rows2 220 221 ≤ 6303708322031933 := by decide +kernel

theorem rows22250R_5753 : rows2 221 223 ≤ 12973497910291622 := by decide +kernel

theorem rows22250R_5754 : rows2 223 225 ≤ 13429464915497877 := by decide +kernel

theorem rows22250R_5755 : rows2 225 227 ≤ 13669955008554315 := by decide +kernel

theorem rows22250R_5756 : rows2 227 229 ≤ 13928999689115776 := by decide +kernel

theorem rows22250R_5757 : rows2 229 231 ≤ 14207280795979581 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5741
#print axioms SieveCert.rows22250R_5757
