/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1992–2003 of 5796

File 192 of 465: the parts `rows22250R_1992` … `rows22250R_2003` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (12 parts, 96578 tests: row 82 columns 58–58, row 82 columns 59–59, row 82 columns
60–60, row 82 columns 61–61, row 82 columns 62–62, row 82 columns 63–63, row 82 columns 64–64, row 82 columns 65–65,
row 82 columns 66–66, row 82 columns 67–67, row 82 columns 68–68, row 82 columns 69–69), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_1992 : rowsJ2 82 83 58 59 ≤ 1121502783214 := by decide +kernel

theorem rows22250R_1993 : rowsJ2 82 83 59 60 ≤ 985352195598 := by decide +kernel

theorem rows22250R_1994 : rowsJ2 82 83 60 61 ≤ 894423603104 := by decide +kernel

theorem rows22250R_1995 : rowsJ2 82 83 61 62 ≤ 756339785748 := by decide +kernel

theorem rows22250R_1996 : rowsJ2 82 83 62 63 ≤ 664001198179 := by decide +kernel

theorem rows22250R_1997 : rowsJ2 82 83 63 64 ≤ 523701526474 := by decide +kernel

theorem rows22250R_1998 : rowsJ2 82 83 64 65 ≤ 429708183420 := by decide +kernel

theorem rows22250R_1999 : rowsJ2 82 83 65 66 ≤ 286901910163 := by decide +kernel

theorem rows22250R_2000 : rowsJ2 82 83 66 67 ≤ 191001498636 := by decide +kernel

theorem rows22250R_2001 : rowsJ2 82 83 67 68 ≤ 95728731908 := by decide +kernel

theorem rows22250R_2002 : rowsJ2 82 83 68 69 ≤ 47720826242 := by decide +kernel

theorem rows22250R_2003 : rowsJ2 82 83 69 70 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1992
#print axioms SieveCert.rows22250R_2003
