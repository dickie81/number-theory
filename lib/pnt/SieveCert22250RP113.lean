/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1084–1091 of 5796

File 113 of 465: the parts `rows22250R_1084` … `rows22250R_1091` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (8 parts, 97008 tests: row 64 columns 52–52, row 64 columns 53–53, row 64 columns
54–54, row 64 columns 55–55, row 64 columns 56–56, row 64 columns 57–57, row 64 columns 58–58, row 64 columns
59–59), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time
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

theorem rows22250R_1084 : rowsJ2 64 65 52 53 ≤ 2810350351274 := by decide +kernel

theorem rows22250R_1085 : rowsJ2 64 65 53 54 ≤ 3681780166476 := by decide +kernel

theorem rows22250R_1086 : rowsJ2 64 65 54 55 ≤ 4572805711041 := by decide +kernel

theorem rows22250R_1087 : rowsJ2 64 65 55 56 ≤ 5646596806487 := by decide +kernel

theorem rows22250R_1088 : rowsJ2 64 65 56 57 ≤ 6881930614780 := by decide +kernel

theorem rows22250R_1089 : rowsJ2 64 65 57 58 ≤ 7992370932173 := by decide +kernel

theorem rows22250R_1090 : rowsJ2 64 65 58 59 ≤ 8959237479669 := by decide +kernel

theorem rows22250R_1091 : rowsJ2 64 65 59 60 ≤ 9857410237803 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1084
#print axioms SieveCert.rows22250R_1091
