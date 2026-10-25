/-
# The refined certificate at `L = 89/40` with `n = 340`, parts 1054–1072 of 4715

File 97 of 351: the parts `rows22250R_1054` … `rows22250R_1072` of `SieveCert22250R.lean`'s certificate on
`SieveGrid22250R.grid22250R` (19 parts, 99503 tests: row 64 columns 29–29, row 64 columns 30–30, row 64 columns
31–31, row 64 columns 32–32, row 64 columns 33–33, row 64 columns 34–34, row 64 columns 35–35, row 64 columns 36–36,
row 64 columns 37–37, row 64 columns 38–38, row 64 columns 39–39, row 64 columns 40–40, row 64 columns 41–41, row 64
columns 42–42, row 64 columns 43–43, row 64 columns 44–44, row 64 columns 45–45, row 64 columns 46–46, row 64
columns 47–47), each a sum of refined costs (`rows2` or `rowsJ2`) at most its bound, by `decide +kernel`, one at a
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

theorem rows22250R_1054 : rowsJ2 64 65 29 30 ≤ 0 := by decide +kernel

theorem rows22250R_1055 : rowsJ2 64 65 30 31 ≤ 0 := by decide +kernel

theorem rows22250R_1056 : rowsJ2 64 65 31 32 ≤ 0 := by decide +kernel

theorem rows22250R_1057 : rowsJ2 64 65 32 33 ≤ 0 := by decide +kernel

theorem rows22250R_1058 : rowsJ2 64 65 33 34 ≤ 0 := by decide +kernel

theorem rows22250R_1059 : rowsJ2 64 65 34 35 ≤ 0 := by decide +kernel

theorem rows22250R_1060 : rowsJ2 64 65 35 36 ≤ 0 := by decide +kernel

theorem rows22250R_1061 : rowsJ2 64 65 36 37 ≤ 0 := by decide +kernel

theorem rows22250R_1062 : rowsJ2 64 65 37 38 ≤ 0 := by decide +kernel

theorem rows22250R_1063 : rowsJ2 64 65 38 39 ≤ 0 := by decide +kernel

theorem rows22250R_1064 : rowsJ2 64 65 39 40 ≤ 0 := by decide +kernel

theorem rows22250R_1065 : rowsJ2 64 65 40 41 ≤ 0 := by decide +kernel

theorem rows22250R_1066 : rowsJ2 64 65 41 42 ≤ 0 := by decide +kernel

theorem rows22250R_1067 : rowsJ2 64 65 42 43 ≤ 0 := by decide +kernel

theorem rows22250R_1068 : rowsJ2 64 65 43 44 ≤ 0 := by decide +kernel

theorem rows22250R_1069 : rowsJ2 64 65 44 45 ≤ 66453706065 := by decide +kernel

theorem rows22250R_1070 : rowsJ2 64 65 45 46 ≤ 260830952282 := by decide +kernel

theorem rows22250R_1071 : rowsJ2 64 65 46 47 ≤ 778149676365 := by decide +kernel

theorem rows22250R_1072 : rowsJ2 64 65 47 48 ≤ 1545284553608 := by decide +kernel

end

end SieveCert

#print axioms SieveCert.rows22250R_1054
#print axioms SieveCert.rows22250R_1072
