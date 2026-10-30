/-
# The certificate to depth 8 at `L = 11/5` with `n = 272`, parts 750–759 of 1136

File 76 of 114: the parts `rows22000E_750` … `rows22000E_759` of `SieveCert22000E.lean`'s certificate on
`SieveGrid22000E.grid22000E` (10 parts, predicted 282 s of the kernel: row 146 columns 48–59, row 146 columns 60–88,
row 146 columns 89–96, row 146 columns 97–104, row 146 columns 105–111, row 146 columns 112–271, row 147 columns
0–47, row 147 columns 48–59, row 147 columns 60–88, row 147 columns 89–96), each a sum of the costs (`rowsJD`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22000E.lean`.
-/
import SieveGrid22000E

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveDeep

open SieveCert

section

attribute [local instance] grid22000E ibPar22000E

theorem rows22000E_750 : rowsJD 146 147 48 60 ≤ 19097587764002 := by decide +kernel

theorem rows22000E_751 : rowsJD 146 147 60 89 ≤ 294430120291612 := by decide +kernel

theorem rows22000E_752 : rowsJD 146 147 89 97 ≤ 489378933286508 := by decide +kernel

theorem rows22000E_753 : rowsJD 146 147 97 105 ≤ 463689957041595 := by decide +kernel

theorem rows22000E_754 : rowsJD 146 147 105 112 ≤ 403313278322158 := by decide +kernel

theorem rows22000E_755 : rowsJD 146 147 112 272 ≤ 1595735467246336 := by decide +kernel

theorem rows22000E_756 : rowsJD 147 148 0 48 ≤ 55211064171001 := by decide +kernel

theorem rows22000E_757 : rowsJD 147 148 48 60 ≤ 18222760527844 := by decide +kernel

theorem rows22000E_758 : rowsJD 147 148 60 89 ≤ 307345895947616 := by decide +kernel

theorem rows22000E_759 : rowsJD 147 148 89 97 ≤ 503404859430771 := by decide +kernel

end

end SieveDeep

#print axioms SieveDeep.rows22000E_750
#print axioms SieveDeep.rows22000E_759
