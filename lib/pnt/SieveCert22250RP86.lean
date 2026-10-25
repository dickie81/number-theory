/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 922–936 of 4715

File 86 of 351: the parts `rows22250R_922` … `rows22250R_936` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (15 parts, 99691 tests: row 61 columns 26–26, row 61 columns 27–27, row 61 columns
28–28, row 61 columns 29–29, row 61 columns 30–30, row 61 columns 31–31, row 61 columns 32–32, row 61 columns 33–33,
row 61 columns 34–34, row 61 columns 35–35, row 61 columns 36–36, row 61 columns 37–37, row 61 columns 38–38, row 61
columns 39–39, row 61 columns 40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by
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

theorem rows22250R_922 : rowsJ2 61 62 26 27 ≤ 0 := by decide +kernel

theorem rows22250R_923 : rowsJ2 61 62 27 28 ≤ 0 := by decide +kernel

theorem rows22250R_924 : rowsJ2 61 62 28 29 ≤ 0 := by decide +kernel

theorem rows22250R_925 : rowsJ2 61 62 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_926 : rowsJ2 61 62 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_927 : rowsJ2 61 62 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_928 : rowsJ2 61 62 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_929 : rowsJ2 61 62 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_930 : rowsJ2 61 62 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_931 : rowsJ2 61 62 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_932 : rowsJ2 61 62 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_933 : rowsJ2 61 62 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_934 : rowsJ2 61 62 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_935 : rowsJ2 61 62 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_936 : rowsJ2 61 62 40 41 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_922
#print axioms SieveCert.rows22250R_936
