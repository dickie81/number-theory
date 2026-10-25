/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 479–486 of 4715

File 47 of 351: the parts `rows22250R_479` … `rows22250R_486` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 98978 tests: row 48 columns 33–33, row 48 columns 34–34, row 48 columns
35–35, row 48 columns 36–36, row 48 columns 37–37, row 48 columns 38–38, row 48 columns 39–39, row 48 columns
40–40), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
(`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_479 : rowsJ2 48 49 33 34 ≤ 62109566196 := by decide +kernel

theorem rows22250R_480 : rowsJ2 48 49 34 35 ≤ 45128949071 := by decide +kernel

theorem rows22250R_481 : rowsJ2 48 49 35 36 ≤ 31070642709 := by decide +kernel

theorem rows22250R_482 : rowsJ2 48 49 36 37 ≤ 19677898902 := by decide +kernel

theorem rows22250R_483 : rowsJ2 48 49 37 38 ≤ 11968032647 := by decide +kernel

theorem rows22250R_484 : rowsJ2 48 49 38 39 ≤ 6884341887 := by decide +kernel

theorem rows22250R_485 : rowsJ2 48 49 39 40 ≤ 5519665613 := by decide +kernel

theorem rows22250R_486 : rowsJ2 48 49 40 41 ≤ 4842071188 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_479
#print axioms SieveCert.rows22250R_486
