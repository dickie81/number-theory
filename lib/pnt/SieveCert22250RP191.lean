/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1984–1991 of 5796

File 191 of 465: the parts `rows22250R_1984` … `rows22250R_1991` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 89750 tests: row 82 columns 50–50, row 82 columns 51–51, row 82 columns
52–52, row 82 columns 53–53, row 82 columns 54–54, row 82 columns 55–55, row 82 columns 56–56, row 82 columns
57–57), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1984 : rowsJ2 82 83 50 51 ≤ 1093254741660 := by decide +kernel

theorem rows22250R_1985 : rowsJ2 82 83 51 52 ≤ 1321469700347 := by decide +kernel

theorem rows22250R_1986 : rowsJ2 82 83 52 53 ≤ 1604529409644 := by decide +kernel

theorem rows22250R_1987 : rowsJ2 82 83 53 54 ≤ 1704277465050 := by decide +kernel

theorem rows22250R_1988 : rowsJ2 82 83 54 55 ≤ 1662220542211 := by decide +kernel

theorem rows22250R_1989 : rowsJ2 82 83 55 56 ≤ 1481640604557 := by decide +kernel

theorem rows22250R_1990 : rowsJ2 82 83 56 57 ≤ 1345753666958 := by decide +kernel

theorem rows22250R_1991 : rowsJ2 82 83 57 58 ≤ 1211260142959 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1984
#print axioms SieveCert.rows22250R_1991
