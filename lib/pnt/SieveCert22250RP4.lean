/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 47–64 of 4715

File 4 of 351: the parts `rows22250R_47` … `rows22250R_64` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (18 parts, work 97775 in units of a depth-4 test: row 24 columns 14–16, row 24 columns
17–18, row 24 columns 19–19, row 24 columns 20–20, row 24 columns 21–21, row 24 columns 22–22, row 24 columns 23–23,
row 24 columns 24–339, row 25 columns 0–13, row 25 columns 14–16, row 25 columns 17–18, row 25 columns 19–19, row 25
columns 20–20, row 25 columns 21–21, row 25 columns 22–22, row 25 columns 23–23, row 25 columns 24–24, row 25
columns 25–339), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_47 : rowsJ2 24 25 14 17 ≤ 1110649103885 := by decide +kernel

theorem rows22250R_48 : rowsJ2 24 25 17 19 ≤ 1922454105955 := by decide +kernel

theorem rows22250R_49 : rowsJ2 24 25 19 20 ≤ 1330408107557 := by decide +kernel

theorem rows22250R_50 : rowsJ2 24 25 20 21 ≤ 1532263742482 := by decide +kernel

theorem rows22250R_51 : rowsJ2 24 25 21 22 ≤ 1701632207261 := by decide +kernel

theorem rows22250R_52 : rowsJ2 24 25 22 23 ≤ 1810518988365 := by decide +kernel

theorem rows22250R_53 : rowsJ2 24 25 23 24 ≤ 1865794490057 := by decide +kernel

theorem rows22250R_54 : rowsJ2 24 25 24 340 ≤ 1886433049005 := by decide +kernel

theorem rows22250R_55 : rowsJ2 25 26 0 14 ≤ 1197538473473 := by decide +kernel

theorem rows22250R_56 : rowsJ2 25 26 14 17 ≤ 1218190118986 := by decide +kernel

theorem rows22250R_57 : rowsJ2 25 26 17 19 ≤ 2000746979924 := by decide +kernel

theorem rows22250R_58 : rowsJ2 25 26 19 20 ≤ 1341043846954 := by decide +kernel

theorem rows22250R_59 : rowsJ2 25 26 20 21 ≤ 1532690089586 := by decide +kernel

theorem rows22250R_60 : rowsJ2 25 26 21 22 ≤ 1675053342310 := by decide +kernel

theorem rows22250R_61 : rowsJ2 25 26 22 23 ≤ 1762814758919 := by decide +kernel

theorem rows22250R_62 : rowsJ2 25 26 23 24 ≤ 1797171023535 := by decide +kernel

theorem rows22250R_63 : rowsJ2 25 26 24 25 ≤ 1819544990612 := by decide +kernel

theorem rows22250R_64 : rowsJ2 25 26 25 340 ≤ 1812730741275 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_47
#print axioms SieveCert.rows22250R_64
