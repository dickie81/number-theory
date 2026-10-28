/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 65–82 of 4715

File 5 of 351: the parts `rows22250R_65` … `rows22250R_82` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, work 96262 in units of a depth-4 test: row 26 columns 0–13, row 26 columns
14–16, row 26 columns 17–18, row 26 columns 19–19, row 26 columns 20–20, row 26 columns 21–21, row 26 columns 22–22,
row 26 columns 23–23, row 26 columns 24–24, row 26 columns 25–25, row 26 columns 26–339, row 27 columns 0–13, row 27
columns 14–16, row 27 columns 17–18, row 27 columns 19–19, row 27 columns 20–20, row 27 columns 21–21, row 27
columns 22–22), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_65 : rowsJ2 26 27 0 14 ≤ 1050992869699 := by decide +kernel

theorem rows22250R_66 : rowsJ2 26 27 14 17 ≤ 1342885618909 := by decide +kernel

theorem rows22250R_67 : rowsJ2 26 27 17 19 ≤ 2059855107310 := by decide +kernel

theorem rows22250R_68 : rowsJ2 26 27 19 20 ≤ 1351104695060 := by decide +kernel

theorem rows22250R_69 : rowsJ2 26 27 20 21 ≤ 1523276000926 := by decide +kernel

theorem rows22250R_70 : rowsJ2 26 27 21 22 ≤ 1644101975704 := by decide +kernel

theorem rows22250R_71 : rowsJ2 26 27 22 23 ≤ 1701559521412 := by decide +kernel

theorem rows22250R_72 : rowsJ2 26 27 23 24 ≤ 1737479853135 := by decide +kernel

theorem rows22250R_73 : rowsJ2 26 27 24 25 ≤ 1748331046108 := by decide +kernel

theorem rows22250R_74 : rowsJ2 26 27 25 26 ≤ 1734508267353 := by decide +kernel

theorem rows22250R_75 : rowsJ2 26 27 26 340 ≤ 1678859004586 := by decide +kernel

theorem rows22250R_76 : rowsJ2 27 28 0 14 ≤ 929469854393 := by decide +kernel

theorem rows22250R_77 : rowsJ2 27 28 14 17 ≤ 1460069037448 := by decide +kernel

theorem rows22250R_78 : rowsJ2 27 28 17 19 ≤ 2110580289205 := by decide +kernel

theorem rows22250R_79 : rowsJ2 27 28 19 20 ≤ 1354687275089 := by decide +kernel

theorem rows22250R_80 : rowsJ2 27 28 20 21 ≤ 1509240569436 := by decide +kernel

theorem rows22250R_81 : rowsJ2 27 28 21 22 ≤ 1599353792868 := by decide +kernel

theorem rows22250R_82 : rowsJ2 27 28 22 23 ≤ 1649098542138 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_65
#print axioms SieveCert.rows22250R_82
