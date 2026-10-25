/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 63–78 of 5796

File 5 of 465: the parts `rows22250R_63` … `rows22250R_78` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 99308 tests: row 25 columns 24–24, row 25 columns 25–359, row 26 columns
0–13, row 26 columns 14–16, row 26 columns 17–18, row 26 columns 19–19, row 26 columns 20–20, row 26 columns 21–21,
row 26 columns 22–22, row 26 columns 23–23, row 26 columns 24–24, row 26 columns 25–25, row 26 columns 26–359, row
27 columns 0–13, row 27 columns 14–16, row 27 columns 17–18), each a sum of refined costs (`rows2` or `rowsJ2`) at
most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_63 : rowsJ2 25 26 24 25 ≤ 1549682945272 := by decide +kernel

theorem rows22250R_64 : rowsJ2 25 26 25 360 ≤ 1578254760586 := by decide +kernel

theorem rows22250R_65 : rowsJ2 26 27 0 14 ≤ 1070784014089 := by decide +kernel

theorem rows22250R_66 : rowsJ2 26 27 14 17 ≤ 575250100979 := by decide +kernel

theorem rows22250R_67 : rowsJ2 26 27 17 19 ≤ 1158248230037 := by decide +kernel

theorem rows22250R_68 : rowsJ2 26 27 19 20 ≤ 892932606778 := by decide +kernel

theorem rows22250R_69 : rowsJ2 26 27 20 21 ≤ 1081391448708 := by decide +kernel

theorem rows22250R_70 : rowsJ2 26 27 21 22 ≤ 1235132110011 := by decide +kernel

theorem rows22250R_71 : rowsJ2 26 27 22 23 ≤ 1362922024498 := by decide +kernel

theorem rows22250R_72 : rowsJ2 26 27 23 24 ≤ 1453165077474 := by decide +kernel

theorem rows22250R_73 : rowsJ2 26 27 24 25 ≤ 1504875741435 := by decide +kernel

theorem rows22250R_74 : rowsJ2 26 27 25 26 ≤ 1518564010059 := by decide +kernel

theorem rows22250R_75 : rowsJ2 26 27 26 360 ≤ 1521334604171 := by decide +kernel

theorem rows22250R_76 : rowsJ2 27 28 0 14 ≤ 928507694685 := by decide +kernel

theorem rows22250R_77 : rowsJ2 27 28 14 17 ≤ 635438028185 := by decide +kernel

theorem rows22250R_78 : rowsJ2 27 28 17 19 ≤ 1238456529164 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_63
#print axioms SieveCert.rows22250R_78
