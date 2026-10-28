/-
# The refined certificate at `L = 278/125` with `n = 340`, parts 63–78 of 5066

File 5 of 387: the parts `rows22240R_63` … `rows22240R_78` of `SieveCert22240R.lean`'s certificate on
`SieveGrid22240R.grid22240R` (16 parts, work 99308 in units of a depth-4 test: row 25 columns 24–24, row 25 columns
25–339, row 26 columns 0–13, row 26 columns 14–16, row 26 columns 17–18, row 26 columns 19–19, row 26 columns 20–20,
row 26 columns 21–21, row 26 columns 22–22, row 26 columns 23–23, row 26 columns 24–24, row 26 columns 25–25, row 26
columns 26–339, row 27 columns 0–13, row 27 columns 14–16, row 27 columns 17–18), each a sum of refined costs
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

theorem rows22240R_63 : rowsJ2 25 26 24 25 ≤ 1935869599134 := by decide +kernel

theorem rows22240R_64 : rowsJ2 25 26 25 340 ≤ 1972154847116 := by decide +kernel

theorem rows22240R_65 : rowsJ2 26 27 0 14 ≤ 1993968354150 := by decide +kernel

theorem rows22240R_66 : rowsJ2 26 27 14 17 ≤ 833384712693 := by decide +kernel

theorem rows22240R_67 : rowsJ2 26 27 17 19 ≤ 1467463076889 := by decide +kernel

theorem rows22240R_68 : rowsJ2 26 27 19 20 ≤ 1114608013503 := by decide +kernel

theorem rows22240R_69 : rowsJ2 26 27 20 21 ≤ 1349877572584 := by decide +kernel

theorem rows22240R_70 : rowsJ2 26 27 21 22 ≤ 1542188393271 := by decide +kernel

theorem rows22240R_71 : rowsJ2 26 27 22 23 ≤ 1702037669234 := by decide +kernel

theorem rows22240R_72 : rowsJ2 26 27 23 24 ≤ 1815278612006 := by decide +kernel

theorem rows22240R_73 : rowsJ2 26 27 24 25 ≤ 1880358720124 := by decide +kernel

theorem rows22240R_74 : rowsJ2 26 27 25 26 ≤ 1898206019958 := by decide +kernel

theorem rows22240R_75 : rowsJ2 26 27 26 340 ≤ 1902318973897 := by decide +kernel

theorem rows22240R_76 : rowsJ2 27 28 0 14 ≤ 1775799120266 := by decide +kernel

theorem rows22240R_77 : rowsJ2 27 28 14 17 ≤ 873078702701 := by decide +kernel

theorem rows22240R_78 : rowsJ2 27 28 17 19 ≤ 1553519334428 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22240R_63
#print axioms SieveCert.rows22240R_78
