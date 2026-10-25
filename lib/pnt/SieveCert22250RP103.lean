/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 976–985 of 5796

File 103 of 465: the parts `rows22250R_976` … `rows22250R_985` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (10 parts, 98209 tests: row 62 columns 29–29, row 62 columns 30–30, row 62 columns
31–31, row 62 columns 32–32, row 62 columns 33–33, row 62 columns 34–34, row 62 columns 35–35, row 62 columns 36–36,
row 62 columns 37–37, row 62 columns 38–38), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
`decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_976 : rowsJ2 62 63 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_977 : rowsJ2 62 63 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_978 : rowsJ2 62 63 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_979 : rowsJ2 62 63 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_980 : rowsJ2 62 63 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_981 : rowsJ2 62 63 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_982 : rowsJ2 62 63 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_983 : rowsJ2 62 63 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_984 : rowsJ2 62 63 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_985 : rowsJ2 62 63 38 39 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_976
#print axioms SieveCert.rows22250R_985
