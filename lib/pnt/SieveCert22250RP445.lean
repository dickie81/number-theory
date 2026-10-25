/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5473–5487 of 5796

File 445 of 465: the parts `rows22250R_5473` … `rows22250R_5487` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 94680 tests: row 183 columns 45–45, row 183 columns 46–46, row 183 columns
47–47, row 183 columns 48–48, row 183 columns 49–49, row 183 columns 50–50, row 183 columns 51–51, row 183 columns
52–52, row 183 columns 53–53, row 183 columns 54–54, row 183 columns 55–55, row 183 columns 56–111, row 183 columns
112–359, row 184 columns 0–37, row 184 columns 38–39), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5473 : rowsJ2 183 184 45 46 ≤ 16101209668528 := by decide +kernel

theorem rows22250R_5474 : rowsJ2 183 184 46 47 ≤ 17632761695222 := by decide +kernel

theorem rows22250R_5475 : rowsJ2 183 184 47 48 ≤ 19215164674736 := by decide +kernel

theorem rows22250R_5476 : rowsJ2 183 184 48 49 ≤ 20847227802263 := by decide +kernel

theorem rows22250R_5477 : rowsJ2 183 184 49 50 ≤ 20636220788302 := by decide +kernel

theorem rows22250R_5478 : rowsJ2 183 184 50 51 ≤ 18637547240580 := by decide +kernel

theorem rows22250R_5479 : rowsJ2 183 184 51 52 ≤ 16758109833409 := by decide +kernel

theorem rows22250R_5480 : rowsJ2 183 184 52 53 ≤ 14994040129390 := by decide +kernel

theorem rows22250R_5481 : rowsJ2 183 184 53 54 ≤ 13341752470613 := by decide +kernel

theorem rows22250R_5482 : rowsJ2 183 184 54 55 ≤ 11797928184080 := by decide +kernel

theorem rows22250R_5483 : rowsJ2 183 184 55 56 ≤ 10359501301809 := by decide +kernel

theorem rows22250R_5484 : rowsJ2 183 184 56 112 ≤ 467241598928776 := by decide +kernel

theorem rows22250R_5485 : rowsJ2 183 184 112 360 ≤ 2197370873653188 := by decide +kernel

theorem rows22250R_5486 : rowsJ2 184 185 0 38 ≤ 14436151034135 := by decide +kernel

theorem rows22250R_5487 : rowsJ2 184 185 38 40 ≤ 15769667043527 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5473
#print axioms SieveCert.rows22250R_5487
