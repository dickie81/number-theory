/-
# The refined certificate at `L = 89/40` with `n = 360`, parts 986–999 of 5796

File 104 of 465: the parts `rows22250R_986` … `rows22250R_999` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (14 parts, 98681 tests: row 62 columns 39–39, row 62 columns 40–40, row 62 columns
41–41, row 62 columns 42–42, row 62 columns 43–43, row 62 columns 44–44, row 62 columns 45–45, row 62 columns 46–46,
row 62 columns 47–47, row 62 columns 48–48, row 62 columns 49–49, row 62 columns 50–50, row 62 columns 51–51, row 62
columns 52–52), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_986 : rowsJ2 62 63 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_987 : rowsJ2 62 63 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_988 : rowsJ2 62 63 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_989 : rowsJ2 62 63 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_990 : rowsJ2 62 63 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_991 : rowsJ2 62 63 44 45 ≤ 0 := by decide +kernel

theorem rows22250R_992 : rowsJ2 62 63 45 46 ≤ 0 := by decide +kernel

theorem rows22250R_993 : rowsJ2 62 63 46 47 ≤ 0 := by decide +kernel

theorem rows22250R_994 : rowsJ2 62 63 47 48 ≤ 110463342038 := by decide +kernel

theorem rows22250R_995 : rowsJ2 62 63 48 49 ≤ 495078908813 := by decide +kernel

theorem rows22250R_996 : rowsJ2 62 63 49 50 ≤ 921901603671 := by decide +kernel

theorem rows22250R_997 : rowsJ2 62 63 50 51 ≤ 1386567264277 := by decide +kernel

theorem rows22250R_998 : rowsJ2 62 63 51 52 ≤ 1995959011811 := by decide +kernel

theorem rows22250R_999 : rowsJ2 62 63 52 53 ≤ 2860625520188 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_986
#print axioms SieveCert.rows22250R_999
