/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5488–5503 of 5796

File 446 of 465: the parts `rows22250R_5488` … `rows22250R_5503` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 98707 tests: row 184 columns 40–41, row 184 columns 42–42, row 184 columns
43–43, row 184 columns 44–44, row 184 columns 45–45, row 184 columns 46–46, row 184 columns 47–47, row 184 columns
48–48, row 184 columns 49–49, row 184 columns 50–50, row 184 columns 51–51, row 184 columns 52–52, row 184 columns
53–53, row 184 columns 54–54, row 184 columns 55–104, row 184 columns 105–359), each a sum of refined costs (`rows2`
or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_5488 : rowsJ2 184 185 40 42 ≤ 21502598909350 := by decide +kernel

theorem rows22250R_5489 : rowsJ2 184 185 42 43 ≤ 12772920072919 := by decide +kernel

theorem rows22250R_5490 : rowsJ2 184 185 43 44 ≤ 14198259765063 := by decide +kernel

theorem rows22250R_5491 : rowsJ2 184 185 44 45 ≤ 15679304182992 := by decide +kernel

theorem rows22250R_5492 : rowsJ2 184 185 45 46 ≤ 17214333703772 := by decide +kernel

theorem rows22250R_5493 : rowsJ2 184 185 46 47 ≤ 18801843319630 := by decide +kernel

theorem rows22250R_5494 : rowsJ2 184 185 47 48 ≤ 20440533701199 := by decide +kernel

theorem rows22250R_5495 : rowsJ2 184 185 48 49 ≤ 22129303511347 := by decide +kernel

theorem rows22250R_5496 : rowsJ2 184 185 49 50 ≤ 20026752452130 := by decide +kernel

theorem rows22250R_5497 : rowsJ2 184 185 50 51 ≤ 18048252935551 := by decide +kernel

theorem rows22250R_5498 : rowsJ2 184 185 51 52 ≤ 16189658208176 := by decide +kernel

theorem rows22250R_5499 : rowsJ2 184 185 52 53 ≤ 14447123613507 := by decide +kernel

theorem rows22250R_5500 : rowsJ2 184 185 53 54 ≤ 12817089206719 := by decide +kernel

theorem rows22250R_5501 : rowsJ2 184 185 54 55 ≤ 11296264036105 := by decide +kernel

theorem rows22250R_5502 : rowsJ2 184 185 55 105 ≤ 18451950754135 := by decide +kernel

theorem rows22250R_5503 : rowsJ2 184 185 105 360 ≤ 2671554991148760 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5488
#print axioms SieveCert.rows22250R_5503
