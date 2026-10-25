/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 694–704 of 5796

File 75 of 465: the parts `rows22250R_694` … `rows22250R_704` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 93968 tests: row 54 columns 47–47, row 54 columns 48–48, row 54 columns
49–49, row 54 columns 50–50, row 54 columns 51–51, row 54 columns 52–52, row 54 columns 53–53, row 54 columns
54–359, row 55 columns 0–14, row 55 columns 15–19, row 55 columns 20–22), each a sum of refined costs (`rows2` or
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

theorem rows22250R_694 : rowsJ2 54 55 47 48 ≤ 118976997487 := by decide +kernel

theorem rows22250R_695 : rowsJ2 54 55 48 49 ≤ 533235741404 := by decide +kernel

theorem rows22250R_696 : rowsJ2 54 55 49 50 ≤ 992954610638 := by decide +kernel

theorem rows22250R_697 : rowsJ2 54 55 50 51 ≤ 1493433087159 := by decide +kernel

theorem rows22250R_698 : rowsJ2 54 55 51 52 ≤ 2149792012004 := by decide +kernel

theorem rows22250R_699 : rowsJ2 54 55 52 53 ≤ 3081100291257 := by decide +kernel

theorem rows22250R_700 : rowsJ2 54 55 53 54 ≤ 4036483898932 := by decide +kernel

theorem rows22250R_701 : rowsJ2 54 55 54 360 ≤ 5013351094021 := by decide +kernel

theorem rows22250R_702 : rowsJ2 55 56 0 15 ≤ 1971978439557 := by decide +kernel

theorem rows22250R_703 : rowsJ2 55 56 15 20 ≤ 1704674355745 := by decide +kernel

theorem rows22250R_704 : rowsJ2 55 56 20 23 ≤ 633402671057 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_694
#print axioms SieveCert.rows22250R_704
