/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 31–46 of 4715

File 3 of 351: the parts `rows22250R_31` … `rows22250R_46` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, work 93964 in units of a depth-4 test: row 22 columns 0–13, row 22 columns
14–16, row 22 columns 17–18, row 22 columns 19–19, row 22 columns 20–20, row 22 columns 21–21, row 22 columns
22–339, row 23 columns 0–13, row 23 columns 14–16, row 23 columns 17–18, row 23 columns 19–19, row 23 columns 20–20,
row 23 columns 21–21, row 23 columns 22–22, row 23 columns 23–339, row 24 columns 0–13), each a sum of refined costs
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

theorem rows22250R_31 : rowsJ2 22 23 0 14 ≤ 1772533027543 := by decide +kernel

theorem rows22250R_32 : rowsJ2 22 23 14 17 ≤ 935803120374 := by decide +kernel

theorem rows22250R_33 : rowsJ2 22 23 17 19 ≤ 1729373259632 := by decide +kernel

theorem rows22250R_34 : rowsJ2 22 23 19 20 ≤ 1284640927619 := by decide +kernel

theorem rows22250R_35 : rowsJ2 22 23 20 21 ≤ 1524237827054 := by decide +kernel

theorem rows22250R_36 : rowsJ2 22 23 21 22 ≤ 1726801355691 := by decide +kernel

theorem rows22250R_37 : rowsJ2 22 23 22 340 ≤ 1884041176943 := by decide +kernel

theorem rows22250R_38 : rowsJ2 23 24 0 14 ≤ 1558230854720 := by decide +kernel

theorem rows22250R_39 : rowsJ2 23 24 14 17 ≤ 1007502353377 := by decide +kernel

theorem rows22250R_40 : rowsJ2 23 24 17 19 ≤ 1833612739312 := by decide +kernel

theorem rows22250R_41 : rowsJ2 23 24 19 20 ≤ 1313191840452 := by decide +kernel

theorem rows22250R_42 : rowsJ2 23 24 20 21 ≤ 1531443677869 := by decide +kernel

theorem rows22250R_43 : rowsJ2 23 24 21 22 ≤ 1714296253166 := by decide +kernel

theorem rows22250R_44 : rowsJ2 23 24 22 23 ≤ 1854102591373 := by decide +kernel

theorem rows22250R_45 : rowsJ2 23 24 23 340 ≤ 1930112439120 := by decide +kernel

theorem rows22250R_46 : rowsJ2 24 25 0 14 ≤ 1365371226105 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_31
#print axioms SieveCert.rows22250R_46
