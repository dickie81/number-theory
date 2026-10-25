/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 1533–1546 of 5796

File 155 of 465: the parts `rows22250R_1533` … `rows22250R_1546` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98218 tests: row 73 columns 68–68, row 73 columns 69–69, row 73 columns
70–70, row 73 columns 71–71, row 73 columns 72–72, row 73 columns 73–359, row 74 columns 0–18, row 74 columns 19–20,
row 74 columns 21–21, row 74 columns 22–22, row 74 columns 23–23, row 74 columns 24–24, row 74 columns 25–25, row 74
columns 26–26), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1533 : rowsJ2 73 74 68 69 ≤ 2999382755928 := by decide +kernel

theorem rows22250R_1534 : rowsJ2 73 74 69 70 ≤ 2765160130147 := by decide +kernel

theorem rows22250R_1535 : rowsJ2 73 74 70 71 ≤ 2532864692372 := by decide +kernel

theorem rows22250R_1536 : rowsJ2 73 74 71 72 ≤ 2294467333968 := by decide +kernel

theorem rows22250R_1537 : rowsJ2 73 74 72 73 ≤ 2057840222874 := by decide +kernel

theorem rows22250R_1538 : rowsJ2 73 74 73 360 ≤ 1814729623123 := by decide +kernel

theorem rows22250R_1539 : rowsJ2 74 75 0 19 ≤ 705146256554 := by decide +kernel

theorem rows22250R_1540 : rowsJ2 74 75 19 21 ≤ 0 := by decide +kernel

theorem rows22250R_1541 : rowsJ2 74 75 21 22 ≤ 0 := by decide +kernel

theorem rows22250R_1542 : rowsJ2 74 75 22 23 ≤ 0 := by decide +kernel

theorem rows22250R_1543 : rowsJ2 74 75 23 24 ≤ 0 := by decide +kernel

theorem rows22250R_1544 : rowsJ2 74 75 24 25 ≤ 0 := by decide +kernel

theorem rows22250R_1545 : rowsJ2 74 75 25 26 ≤ 0 := by decide +kernel

theorem rows22250R_1546 : rowsJ2 74 75 26 27 ≤ 0 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1533
#print axioms SieveCert.rows22250R_1546
