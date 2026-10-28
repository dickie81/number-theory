/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 130–145 of 5066

File 9 of 387: the parts `rows22240R_130` … `rows22240R_145` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 94944 in units of a depth-4 test: row 31 columns 0–13, row 31 columns
14–16, row 31 columns 17–18, row 31 columns 19–19, row 31 columns 20–20, row 31 columns 21–21, row 31 columns 22–22,
row 31 columns 23–23, row 31 columns 24–24, row 31 columns 25–25, row 31 columns 26–26, row 31 columns 27–27, row 31
columns 28–28, row 31 columns 29–29, row 31 columns 30–30, row 31 columns 31–339), each a sum of refined costs
(`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22240R.lean`.
-/
import SieveGrid22240R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22240R

theorem rows22240R_130 : rowsJ2 31 32 0 14 ≤ 1091091061073 := by decide +kernel

theorem rows22240R_131 : rowsJ2 31 32 14 17 ≤ 1205801003522 := by decide +kernel

theorem rows22240R_132 : rowsJ2 31 32 17 19 ≤ 1846517969195 := by decide +kernel

theorem rows22240R_133 : rowsJ2 31 32 19 20 ≤ 1210066394006 := by decide +kernel

theorem rows22240R_134 : rowsJ2 31 32 20 21 ≤ 1363560449698 := by decide +kernel

theorem rows22240R_135 : rowsJ2 31 32 21 22 ≤ 1471112437320 := by decide +kernel

theorem rows22240R_136 : rowsJ2 31 32 22 23 ≤ 1521948840884 := by decide +kernel

theorem rows22240R_137 : rowsJ2 31 32 23 24 ≤ 1553589063569 := by decide +kernel

theorem rows22240R_138 : rowsJ2 31 32 24 25 ≤ 1562844686040 := by decide +kernel

theorem rows22240R_139 : rowsJ2 31 32 25 26 ≤ 1550153124372 := by decide +kernel

theorem rows22240R_140 : rowsJ2 31 32 26 27 ≤ 1500134408446 := by decide +kernel

theorem rows22240R_141 : rowsJ2 31 32 27 28 ≤ 1437138609140 := by decide +kernel

theorem rows22240R_142 : rowsJ2 31 32 28 29 ≤ 1364138823271 := by decide +kernel

theorem rows22240R_143 : rowsJ2 31 32 29 30 ≤ 1288809893032 := by decide +kernel

theorem rows22240R_144 : rowsJ2 31 32 30 31 ≤ 1211641147658 := by decide +kernel

theorem rows22240R_145 : rowsJ2 31 32 31 340 ≤ 1147885830693 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_130
#print axioms SieveCert.rows22240R_145
