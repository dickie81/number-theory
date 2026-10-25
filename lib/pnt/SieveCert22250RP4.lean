/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 47–62 of 5796

File 4 of 465: the parts `rows22250R_47` … `rows22250R_62` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (16 parts, 96091 tests: row 24 columns 14–16, row 24 columns 17–18, row 24 columns
19–19, row 24 columns 20–20, row 24 columns 21–21, row 24 columns 22–22, row 24 columns 23–23, row 24 columns
24–359, row 25 columns 0–13, row 25 columns 14–16, row 25 columns 17–18, row 25 columns 19–19, row 25 columns 20–20,
row 25 columns 21–21, row 25 columns 22–22, row 25 columns 23–23), each a sum of refined costs (`rows2` or `rowsJ2`)
at most its bound, by `decide +kernel`, one at a time (`Elab.async false`).

The file imports `SieveGrid22250R.lean`.
-/
import SieveGrid22250R

/-! The kernel checks run one at a time: with asynchronous elaboration they would run together and need the
memory of the whole file. -/
set_option Elab.async false

namespace SieveCert

section

attribute [local instance] grid22250R

theorem rows22250R_47 : rowsJ2 24 25 14 17 ≤ 491331287130 := by decide +kernel

theorem rows22250R_48 : rowsJ2 24 25 17 19 ≤ 1021438259670 := by decide +kernel

theorem rows22250R_49 : rowsJ2 24 25 19 20 ≤ 818156414191 := by decide +kernel

theorem rows22250R_50 : rowsJ2 24 25 20 21 ≤ 1036555320106 := by decide +kernel

theorem rows22250R_51 : rowsJ2 24 25 21 22 ≤ 1227936150610 := by decide +kernel

theorem rows22250R_52 : rowsJ2 24 25 22 23 ≤ 1382103213822 := by decide +kernel

theorem rows22250R_53 : rowsJ2 24 25 23 24 ≤ 1503404856088 := by decide +kernel

theorem rows22250R_54 : rowsJ2 24 25 24 360 ≤ 1591878948057 := by decide +kernel

theorem rows22250R_55 : rowsJ2 25 26 0 14 ≤ 1228059424714 := by decide +kernel

theorem rows22250R_56 : rowsJ2 25 26 14 17 ≤ 530574515187 := by decide +kernel

theorem rows22250R_57 : rowsJ2 25 26 17 19 ≤ 1082393533023 := by decide +kernel

theorem rows22250R_58 : rowsJ2 25 26 19 20 ≤ 858424164107 := by decide +kernel

theorem rows22250R_59 : rowsJ2 25 26 20 21 ≤ 1063005166693 := by decide +kernel

theorem rows22250R_60 : rowsJ2 25 26 21 22 ≤ 1233873617233 := by decide +kernel

theorem rows22250R_61 : rowsJ2 25 26 22 23 ≤ 1373746219427 := by decide +kernel

theorem rows22250R_62 : rowsJ2 25 26 23 24 ≤ 1483205131047 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_47
#print axioms SieveCert.rows22250R_62
