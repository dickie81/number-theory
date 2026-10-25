/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 210–218 of 5796

File 14 of 465: the parts `rows22250R_210` … `rows22250R_218` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (9 parts, 95994 tests: row 35 columns 30–30, row 35 columns 31–31, row 35 columns
32–32, row 35 columns 33–33, row 35 columns 34–34, row 35 columns 35–359, row 36 columns 0–13, row 36 columns 14–16,
row 36 columns 17–18), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one
at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_210 : rowsJ2 35 36 30 31 ≤ 682721922597 := by decide +kernel

theorem rows22250R_211 : rowsJ2 35 36 31 32 ≤ 641864836850 := by decide +kernel

theorem rows22250R_212 : rowsJ2 35 36 32 33 ≤ 617799006689 := by decide +kernel

theorem rows22250R_213 : rowsJ2 35 36 33 34 ≤ 620060491528 := by decide +kernel

theorem rows22250R_214 : rowsJ2 35 36 34 35 ≤ 649048497084 := by decide +kernel

theorem rows22250R_215 : rowsJ2 35 36 35 360 ≤ 710346698106 := by decide +kernel

theorem rows22250R_216 : rowsJ2 36 37 0 14 ≤ 410351014911 := by decide +kernel

theorem rows22250R_217 : rowsJ2 36 37 14 17 ≤ 1359015008222 := by decide +kernel

theorem rows22250R_218 : rowsJ2 36 37 17 19 ≤ 1599921166108 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_210
#print axioms SieveCert.rows22250R_218
