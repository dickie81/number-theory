/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 5695–5709 of 5796

File 459 of 465: the parts `rows22250R_5695` … `rows22250R_5709` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 96425 tests: row 199 columns 41–359, row 200 columns 0–32, row 200 columns
33–34, row 200 columns 35–36, row 200 columns 37–37, row 200 columns 38–38, row 200 columns 39–39, row 200 columns
40–359, row 201 columns 0–31, row 201 columns 32–34, row 201 columns 35–36, row 201 columns 37–37, row 201 columns
38–38, row 201 columns 39–359, row 202 columns 0–31), each a sum of refined costs (`rows2` or `rowsJ2`) at most its
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

theorem rows22250R_5695 : rowsJ2 199 200 41 360 ≤ 3996980216222110 := by decide +kernel

theorem rows22250R_5696 : rowsJ2 200 201 0 33 ≤ 20318162250871 := by decide +kernel

theorem rows22250R_5697 : rowsJ2 200 201 33 35 ≤ 21000607437735 := by decide +kernel

theorem rows22250R_5698 : rowsJ2 200 201 35 37 ≤ 32072910370534 := by decide +kernel

theorem rows22250R_5699 : rowsJ2 200 201 37 38 ≤ 20983017828556 := by decide +kernel

theorem rows22250R_5700 : rowsJ2 200 201 38 39 ≤ 24698357929394 := by decide +kernel

theorem rows22250R_5701 : rowsJ2 200 201 39 40 ≤ 28686954577985 := by decide +kernel

theorem rows22250R_5702 : rowsJ2 200 201 40 360 ≤ 4112927795925721 := by decide +kernel

theorem rows22250R_5703 : rowsJ2 201 202 0 32 ≤ 15565240407181 := by decide +kernel

theorem rows22250R_5704 : rowsJ2 201 202 32 35 ≤ 30897377010988 := by decide +kernel

theorem rows22250R_5705 : rowsJ2 201 202 35 37 ≤ 34635546009202 := by decide +kernel

theorem rows22250R_5706 : rowsJ2 201 202 37 38 ≤ 22481759794250 := by decide +kernel

theorem rows22250R_5707 : rowsJ2 201 202 38 39 ≤ 26405125037648 := by decide +kernel

theorem rows22250R_5708 : rowsJ2 201 202 39 360 ≤ 4225631155621628 := by decide +kernel

theorem rows22250R_5709 : rowsJ2 202 203 0 32 ≤ 18234093425391 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_5695
#print axioms SieveCert.rows22250R_5709
