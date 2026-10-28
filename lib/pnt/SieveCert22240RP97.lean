/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 979–989 of 5066

File 97 of 387: the parts `rows22240R_979` … `rows22240R_989` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (11 parts, work 97978 in units of a depth-4 test: row 61 columns 59–59, row 61 columns
60–60, row 61 columns 61–339, row 62 columns 0–16, row 62 columns 17–20, row 62 columns 21–22, row 62 columns 23–23,
row 62 columns 24–24, row 62 columns 25–25, row 62 columns 26–26, row 62 columns 27–27), each a sum of refined costs
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

theorem rows22240R_979 : rowsJ2 61 62 59 60 ≤ 13580743031379 := by decide +kernel

theorem rows22240R_980 : rowsJ2 61 62 60 61 ≤ 14488174180881 := by decide +kernel

theorem rows22240R_981 : rowsJ2 61 62 61 340 ≤ 14628101788739 := by decide +kernel

theorem rows22240R_982 : rowsJ2 62 63 0 17 ≤ 2700278424382 := by decide +kernel

theorem rows22240R_983 : rowsJ2 62 63 17 21 ≤ 553271413659 := by decide +kernel

theorem rows22240R_984 : rowsJ2 62 63 21 23 ≤ 148718322513 := by decide +kernel

theorem rows22240R_985 : rowsJ2 62 63 23 24 ≤ 49492674921 := by decide +kernel

theorem rows22240R_986 : rowsJ2 62 63 24 25 ≤ 37047248293 := by decide +kernel

theorem rows22240R_987 : rowsJ2 62 63 25 26 ≤ 24715897346 := by decide +kernel

theorem rows22240R_988 : rowsJ2 62 63 26 27 ≤ 16447028339 := by decide +kernel

theorem rows22240R_989 : rowsJ2 62 63 27 28 ≤ 8240243696 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_979
#print axioms SieveCert.rows22240R_989
