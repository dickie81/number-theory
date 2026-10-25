/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 844–854 of 5796

File 90 of 465: the parts `rows22250R_844` … `rows22250R_854` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (11 parts, 96604 tests: row 58 columns 55–55, row 58 columns 56–56, row 58 columns
57–57, row 58 columns 58–359, row 59 columns 0–15, row 59 columns 16–20, row 59 columns 21–23, row 59 columns 24–24,
row 59 columns 25–25, row 59 columns 26–26, row 59 columns 27–27), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_844 : rowsJ2 58 59 55 56 ≤ 5960882296353 := by decide +kernel

theorem rows22250R_845 : rowsJ2 58 59 56 57 ≤ 7345180274088 := by decide +kernel

theorem rows22250R_846 : rowsJ2 58 59 57 58 ≤ 8796800792850 := by decide +kernel

theorem rows22250R_847 : rowsJ2 58 59 58 360 ≤ 10179061085549 := by decide +kernel

theorem rows22250R_848 : rowsJ2 59 60 0 16 ≤ 2201069585346 := by decide +kernel

theorem rows22250R_849 : rowsJ2 59 60 16 21 ≤ 942414376116 := by decide +kernel

theorem rows22250R_850 : rowsJ2 59 60 21 24 ≤ 292296477863 := by decide +kernel

theorem rows22250R_851 : rowsJ2 59 60 24 25 ≤ 64046056982 := by decide +kernel

theorem rows22250R_852 : rowsJ2 59 60 25 26 ≤ 51140899084 := by decide +kernel

theorem rows22250R_853 : rowsJ2 59 60 26 27 ≤ 38357193601 := by decide +kernel

theorem rows22250R_854 : rowsJ2 59 60 27 28 ≤ 28723764590 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_844
#print axioms SieveCert.rows22250R_854
